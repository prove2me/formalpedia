-- Prove2me | Definitions.Def_RHGram665_20261117_Shared_P02_v1
-- name    : RHGram665_20261117_Shared_P02_v1
-- status  : Definition
-- author  : @bueno_ricardo
-- created : 2026-11-17T23:13:14.278987+00:00
-- url     : https://prove2.me/theorems/4fc8a1ae-25a8-4cd9-8996-570adb3d9562
-- title:
--   Gram 665 ordinary shared terms, part 2
-- statement:
--   Exact shared expressions and complete ordinary auxiliary proofs for the endpoint certificate of Gram point 665. No additional axioms or custom proof generators. Imports the already published analytic and numerical support modules.
-- source:
--   Salvatore Mercuri and Bhavik Mehta, smmercuri/zeta commit 3dab6480a82f1bfc5de0a59550e279cf50490033; Apache-2.0. Ordinary proof export and exact sharing by Desenvolvimento RH. Full expanded strict AXLE and cumulative prefixes: 24b9b338-7815-48ce-96ac-d0a33d0ecb6c.

import Definitions.Def_RHGram665_20261117_Shared_P01_v1
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
noncomputable def Gram665ProofSharing.c224 := (Complex.Stirling.logGammaStirling (nat_lit 2) Gram665ProofSharing.c47)

noncomputable def Gram665ProofSharing.c225 := (@HDiv.hDiv.{0, 0, 0} Real Real Real Gram665ProofSharing.c15 Gram665ProofSharing.c39 Gram665ProofSharing.c6)

noncomputable def Gram665ProofSharing.c226 := (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) Gram665ProofSharing.c225 (Real.log Real.pi))

noncomputable def Gram665ProofSharing.c227 := (nat_lit 264803210913070413031441116200152189359229570307)

noncomputable def Gram665ProofSharing.c228 := (nat_lit 39560581191298328454224758719035407290007)

noncomputable def Gram665ProofSharing.c229 := (nat_lit 4771059982349598834761081333467704416277653)

noncomputable def Gram665ProofSharing.c230 := (nat_lit 5942112188569825319515796275200000000000)

noncomputable def Gram665ProofSharing.c231 := (nat_lit 44536919768911699213537357926625112743679)

noncomputable def Gram665ProofSharing.c232 := (nat_lit 591890081283322443936143769600000000000000000000)

noncomputable def Gram665ProofSharing.c233 := (@HDiv.hDiv.{0, 0, 0} Complex Complex Complex Gram665ProofSharing.c28 Gram665ProofSharing.c30 Gram665ProofSharing.c42)

noncomputable def Gram665ProofSharing.c234 := (@HSub.hSub.{0, 0, 0} Complex Complex Complex (@instHSub.{0} Complex Complex.instSub) Gram665ProofSharing.c47 Gram665ProofSharing.c233)

noncomputable def Gram665ProofSharing.c235 := (Complex.log Gram665ProofSharing.c47)

noncomputable def Gram665ProofSharing.c236 := (@HMul.hMul.{0, 0, 0} Complex Complex Complex (@instHMul.{0} Complex Complex.instMul) Gram665ProofSharing.c234 Gram665ProofSharing.c235)

noncomputable def Gram665ProofSharing.c237 := (@HSub.hSub.{0, 0, 0} Complex Complex Complex (@instHSub.{0} Complex Complex.instSub) Gram665ProofSharing.c236 Gram665ProofSharing.c47)

noncomputable def Gram665ProofSharing.c238 := (@HMul.hMul.{0, 0, 0} Complex Complex Complex (@instHMul.{0} Complex Complex.instMul) Gram665ProofSharing.c233 ↑Gram665ProofSharing.c8)

noncomputable def Gram665ProofSharing.c239 := (@HAdd.hAdd.{0, 0, 0} Complex Complex Complex (@instHAdd.{0} Complex Complex.instAdd) Gram665ProofSharing.c237 Gram665ProofSharing.c238)

noncomputable def Gram665ProofSharing.c240 := (@DivInvMonoid.toZPow.{0} Complex Complex.instDivInvMonoid)

noncomputable def Gram665ProofSharing.c241 := (@ZPow.toPow.{0} Complex Gram665ProofSharing.c240)

noncomputable def Gram665ProofSharing.c242 := (@instHPow.{0, 0} Complex Int Gram665ProofSharing.c241)

noncomputable def Gram665ProofSharing.c243 := (@OfNat.ofNat.{0} Int (nat_lit 1) (@instOfNat (nat_lit 1)))

noncomputable def Gram665ProofSharing.c244 := (@OfNat.ofNat.{0} Int (nat_lit 2) (@instOfNat (nat_lit 2)))

noncomputable def Gram665ProofSharing.c245 := (nat_lit 474552229918624131623031711722347)

noncomputable def Gram665ProofSharing.c246 := (nat_lit 17826336565709475958547388825600000000000)

noncomputable def Gram665ProofSharing.c247 := (nat_lit 16158478893521940853400346703440770429693)

noncomputable def Gram665ProofSharing.c248 := (BSN.w_sub_half_zero_mk Gram665ProofSharing.c39 Bool.false (nat_lit 102149871) (nat_lit 100000) Gram665ProofSharing.c56 (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram665ProofSharing.c249 := (Enclosure.sfrac Bool.true (nat_lit 100000) (nat_lit 400000))

noncomputable def Gram665ProofSharing.c250 := (Enclosure.Real.IsNear.const Bool.true (nat_lit 100000) (nat_lit 400000))

noncomputable def Gram665ProofSharing.c251 := (@Enclosure.Complex.IsNear.mk Gram665ProofSharing.c249 Gram665ProofSharing.c59 Bool.true (nat_lit 100000) (nat_lit 400000) (nat_lit 0) (nat_lit 1) Bool.false (nat_lit 204299742) (nat_lit 400000) (nat_lit 0) (nat_lit 1) Gram665ProofSharing.c250 Gram665ProofSharing.c61)

noncomputable def Gram665ProofSharing.c252 := (@Enclosure.Complex.IsNear.of_eq Gram665ProofSharing.c234 { re := Enclosure.sfrac Bool.true (nat_lit 100000) (nat_lit 400000), im := Enclosure.sfrac Bool.false (nat_lit 204299742) (nat_lit 400000) } Bool.true (nat_lit 100000) (nat_lit 400000) (nat_lit 0) (nat_lit 1) Bool.false (nat_lit 204299742) (nat_lit 400000) (nat_lit 0) (nat_lit 1) Gram665ProofSharing.c248 Gram665ProofSharing.c251)

noncomputable def Gram665ProofSharing.c253 := (@Enclosure.Complex.IsNear.re_isNear Gram665ProofSharing.c234 Bool.true (nat_lit 100000) (nat_lit 400000) (nat_lit 0) (nat_lit 1) Bool.false (nat_lit 204299742) (nat_lit 400000) (nat_lit 0) (nat_lit 1) Gram665ProofSharing.c252)

noncomputable def Gram665ProofSharing.c254 := (Complex.log { re := Enclosure.sfrac Bool.false (nat_lit 100000) (nat_lit 400000), im := Enclosure.sfrac Bool.false (nat_lit 204299742) (nat_lit 400000) })

noncomputable def Gram665ProofSharing.c255 := (@congrArg.{1, 1} Complex Complex Gram665ProofSharing.c47 { re := Enclosure.sfrac Bool.false (nat_lit 100000) (nat_lit 400000), im := Enclosure.sfrac Bool.false (nat_lit 204299742) (nat_lit 400000) } Complex.log Gram665ProofSharing.c57)

noncomputable def Gram665ProofSharing.c256 := (Enclosure.sfrac Bool.false (nat_lit 1) (nat_lit 2))

noncomputable def Gram665ProofSharing.c257 := (Enclosure.sfrac Bool.false (nat_lit 41738394581266564) (nat_lit 160000000000))

noncomputable def Gram665ProofSharing.c258 := (Real.log Gram665ProofSharing.c257)

noncomputable def Gram665ProofSharing.c259 := (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) Gram665ProofSharing.c256 Gram665ProofSharing.c258)

noncomputable def Gram665ProofSharing.c260 := (Enclosure.clog_re_eq (nat_lit 100000) (nat_lit 204299742) (nat_lit 400000) (nat_lit 41738394581266564) (nat_lit 160000000000) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram665ProofSharing.c261 := (Enclosure.Real.IsNear.const Bool.false (nat_lit 1) (nat_lit 2))

noncomputable def Gram665ProofSharing.c262 := (@Nat.cast.{0} Real Real.instNatCast (nat_lit 41738394581266564))

noncomputable def Gram665ProofSharing.c263 := (@Nat.cast.{0} Real Real.instNatCast (nat_lit 160000000000))

noncomputable def Gram665ProofSharing.c264 := (@HDiv.hDiv.{0, 0, 0} Real Real Real Gram665ProofSharing.c15 Gram665ProofSharing.c262 Gram665ProofSharing.c263)

noncomputable def Gram665ProofSharing.c265 := (Real.log Gram665ProofSharing.c264)

noncomputable def Gram665ProofSharing.c266 := (nat_lit 12162003003916678705576397795267719984768846285295349389904925043698424514882282860266271787252891505297110150617396838516085603224620362913528840475648374429351898780777071832074611491191541116218794913899882124042995079608561803297413087698720049935123812757024823060355855541947018170532154765004824479702339936261359919937537670274247504691200)

noncomputable def Gram665ProofSharing.c267 := (nat_lit 476343450720930441804686240769887331315798006361158546072305027301273521198394349527033980414484201972844507544344586484980957179885604344689110783593293903549326103332088904086606550261382070120184776109292268220734077694982367284556130136512363262053835254938036753329980266389599482806271486295971368928968092923701422011395620928441622200320)

noncomputable def Gram665ProofSharing.c268 := (nat_lit 145708345987104399875839923384980497279532749506357808939440622448118782263065818034099885444944562615867976758597342534645753589768468612717444628718771540679528907776563756689806951242587222249224204378355613026527059327078129802143983124514454108795867417573286790221385502614383554270940097484123621081185568459576772077821309747200)

noncomputable def Gram665ProofSharing.c269 := (BSN.artanhP (nat_lit 20766874581266564))

noncomputable def Gram665ProofSharing.c270 := (BSN.artanhQ (nat_lit 62709914581266564))

noncomputable def Gram665ProofSharing.c271 := (@BSN.binarySplit_of_base10 Gram665ProofSharing.c269 Gram665ProofSharing.c270 (nat_lit 0) (nat_lit 10) Gram665ProofSharing.c267 Gram665ProofSharing.c266 Gram665ProofSharing.c268 (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram665ProofSharing.c272 := (BSN.log_dyadic_bound (nat_lit 20766874581266564) (nat_lit 62709914581266564) (nat_lit 11) (nat_lit 10) Gram665ProofSharing.c266 (nat_lit 17179869184) (nat_lit 6800000000) Gram665ProofSharing.c267 Gram665ProofSharing.c268 (nat_lit 11824149965) (nat_lit 83476789162533128) (nat_lit 41943040000000000) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) Gram665ProofSharing.c271 (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram665ProofSharing.c273 := (BSN.log_rat_reduce_isNear (nat_lit 41738394581266564) (nat_lit 160000000000) (nat_lit 17) (nat_lit 83476789162533128) (nat_lit 41943040000000000) (nat_lit 11824149965) (nat_lit 17179869184) (nat_lit 24973259072661432) (nat_lit 36028797018963968) (nat_lit 6800000000) (nat_lit 1000000000000000) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) Gram665ProofSharing.c272 BSN.log2_near_15 (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram665ProofSharing.c274 := (@Enclosure.Real.IsNear.recentre' Gram665ProofSharing.c265 Bool.false (nat_lit 7719644406440672298759356416) (nat_lit 618970019642690137449562112) (nat_lit 1000115600000000) (nat_lit 6800000000000000000000000) (nat_lit 56167805497830503) (nat_lit 4503599627370496) (nat_lit 2500289) (nat_lit 17000000000000000) Gram665ProofSharing.c273 (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram665ProofSharing.c275 := (BSN.isNear_log_sfrac (nat_lit 41738394581266564) (nat_lit 160000000000) (nat_lit 56167805497830503) (nat_lit 4503599627370496) (nat_lit 2500289) (nat_lit 17000000000000000) Bool.false Gram665ProofSharing.c274)

noncomputable def Gram665ProofSharing.c276 := (@Enclosure.Real.IsNear.mulLit_ff Gram665ProofSharing.c256 Gram665ProofSharing.c258 (nat_lit 1) (nat_lit 2) (nat_lit 0) (nat_lit 1) (nat_lit 56167805497830503) (nat_lit 4503599627370496) (nat_lit 2500289) (nat_lit 17000000000000000) (nat_lit 56167805497830503) (nat_lit 9007199254740992) (nat_lit 2500289) (nat_lit 34000000000000000) Gram665ProofSharing.c261 Gram665ProofSharing.c275 (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram665ProofSharing.c277 := (@Enclosure.Real.IsNear.of_eq (Gram665ProofSharing.c254 : ℂ).re Gram665ProofSharing.c259 Bool.false (nat_lit 56167805497830503) (nat_lit 9007199254740992) (nat_lit 2500289) (nat_lit 34000000000000000) Gram665ProofSharing.c260 Gram665ProofSharing.c276)

noncomputable def Gram665ProofSharing.c278 := (@Nat.cast.{0} Real Real.instNatCast (nat_lit 204299742))

noncomputable def Gram665ProofSharing.c279 := (@Nat.cast.{0} Real Real.instNatCast (nat_lit 100000))

noncomputable def Gram665ProofSharing.c280 := (@HDiv.hDiv.{0, 0, 0} Real Real Real Gram665ProofSharing.c15 Gram665ProofSharing.c278 Gram665ProofSharing.c279)

noncomputable def Gram665ProofSharing.c281 := (Real.arctan Gram665ProofSharing.c280)

noncomputable def Gram665ProofSharing.c282 := (Enclosure.clog_im_eq (nat_lit 100000) (nat_lit 204299742) (nat_lit 400000) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram665ProofSharing.c283 := (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) Gram665ProofSharing.c256 Real.pi)

noncomputable def Gram665ProofSharing.c284 := (@HDiv.hDiv.{0, 0, 0} Real Real Real Gram665ProofSharing.c15 Gram665ProofSharing.c279 Gram665ProofSharing.c278)

noncomputable def Gram665ProofSharing.c285 := (Real.arctan Gram665ProofSharing.c284)

noncomputable def Gram665ProofSharing.c286 := (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) Gram665ProofSharing.c283 Gram665ProofSharing.c285)

noncomputable def Gram665ProofSharing.c287 := (BSN.arctan_recip (nat_lit 204299742) (nat_lit 100000) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram665ProofSharing.c288 := (@Enclosure.Real.IsNear.mulLit_ff Gram665ProofSharing.c256 Real.pi (nat_lit 1) (nat_lit 2) (nat_lit 0) (nat_lit 1) (nat_lit 226375608064910080) (nat_lit 72057594037927936) (nat_lit 1) (nat_lit 1000000000000000) (nat_lit 884279719003555) (nat_lit 562949953421312) (nat_lit 1) (nat_lit 2000000000000000) Gram665ProofSharing.c261 BSN.pi_near_15 (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram665ProofSharing.c289 := (@BSN.binarySplit_of_le (BSN.arctanEvenP (nat_lit 100000)) (BSN.arctanEvenQ (nat_lit 204299742)) (nat_lit 0) (nat_lit 0) (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram665ProofSharing.c290 := (@BSN.binarySplit_of_le (BSN.arctanOddP (nat_lit 100000)) (BSN.arctanOddQ (nat_lit 204299742)) (nat_lit 0) (nat_lit 0) (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram665ProofSharing.c291 := (BSN.arctan_dyadic_bound_f (nat_lit 100000) (nat_lit 204299742) (nat_lit 1) (nat_lit 0) (nat_lit 17179869184) (nat_lit 6800000000) (nat_lit 0) (nat_lit 1) (nat_lit 1) (nat_lit 0) (nat_lit 1) (nat_lit 1) (nat_lit 8409148) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) Gram665ProofSharing.c289 Gram665ProofSharing.c290 (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram665ProofSharing.c292 := (@Enclosure.Real.IsNear.subLit_ff_p Gram665ProofSharing.c283 Gram665ProofSharing.c285 (nat_lit 884279719003555) (nat_lit 562949953421312) (nat_lit 1) (nat_lit 2000000000000000) (nat_lit 8409148) (nat_lit 17179869184) (nat_lit 1) (nat_lit 6800000000) (nat_lit 15187075965070440811986944) (nat_lit 884004168041891) (nat_lit 562949953421312) (nat_lit 5000017) (nat_lit 34000000000000000) Gram665ProofSharing.c288 Gram665ProofSharing.c291 (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram665ProofSharing.c293 := (@Enclosure.Real.IsNear.of_eq Gram665ProofSharing.c281 Gram665ProofSharing.c286 Bool.false (nat_lit 884004168041891) (nat_lit 562949953421312) (nat_lit 5000017) (nat_lit 34000000000000000) Gram665ProofSharing.c287 Gram665ProofSharing.c292)

noncomputable def Gram665ProofSharing.c294 := (@Enclosure.Real.IsNear.of_eq (Gram665ProofSharing.c254 : ℂ).im Gram665ProofSharing.c281 Bool.false (nat_lit 884004168041891) (nat_lit 562949953421312) (nat_lit 5000017) (nat_lit 34000000000000000) Gram665ProofSharing.c282 Gram665ProofSharing.c293)

noncomputable def Gram665ProofSharing.c295 := (@Enclosure.Complex.IsNear.of_parts Gram665ProofSharing.c254 Bool.false (nat_lit 56167805497830503) (nat_lit 9007199254740992) (nat_lit 2500289) (nat_lit 34000000000000000) Bool.false (nat_lit 884004168041891) (nat_lit 562949953421312) (nat_lit 5000017) (nat_lit 34000000000000000) Gram665ProofSharing.c277 Gram665ProofSharing.c294)

noncomputable def Gram665ProofSharing.c296 := (@Enclosure.Complex.IsNear.of_eq Gram665ProofSharing.c235 Gram665ProofSharing.c254 Bool.false (nat_lit 56167805497830503) (nat_lit 9007199254740992) (nat_lit 2500289) (nat_lit 34000000000000000) Bool.false (nat_lit 884004168041891) (nat_lit 562949953421312) (nat_lit 5000017) (nat_lit 34000000000000000) Gram665ProofSharing.c255 Gram665ProofSharing.c295)

noncomputable def Gram665ProofSharing.c297 := (@Enclosure.Complex.IsNear.re_isNear Gram665ProofSharing.c235 Bool.false (nat_lit 56167805497830503) (nat_lit 9007199254740992) (nat_lit 2500289) (nat_lit 34000000000000000) Bool.false (nat_lit 884004168041891) (nat_lit 562949953421312) (nat_lit 5000017) (nat_lit 34000000000000000) Gram665ProofSharing.c296)

noncomputable def Gram665ProofSharing.c298 := (@Enclosure.Complex.IsNear.im_isNear Gram665ProofSharing.c234 Bool.true (nat_lit 100000) (nat_lit 400000) (nat_lit 0) (nat_lit 1) Bool.false (nat_lit 204299742) (nat_lit 400000) (nat_lit 0) (nat_lit 1) Gram665ProofSharing.c252)

noncomputable def Gram665ProofSharing.c299 := (@Enclosure.Complex.IsNear.im_isNear Gram665ProofSharing.c235 Bool.false (nat_lit 56167805497830503) (nat_lit 9007199254740992) (nat_lit 2500289) (nat_lit 34000000000000000) Bool.false (nat_lit 884004168041891) (nat_lit 562949953421312) (nat_lit 5000017) (nat_lit 34000000000000000) Gram665ProofSharing.c296)

noncomputable def Gram665ProofSharing.c300 := (↑Gram665ProofSharing.c8)

noncomputable def Gram665ProofSharing.c301 := (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) (Gram665ProofSharing.c233 : ℂ).re (Gram665ProofSharing.c300 : ℂ).re)

noncomputable def Gram665ProofSharing.c302 := (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) (Gram665ProofSharing.c233 : ℂ).im (Gram665ProofSharing.c300 : ℂ).im)

noncomputable def Gram665ProofSharing.c303 := (Enclosure.sfrac Bool.false (nat_lit 0) (nat_lit 1))

noncomputable def Gram665ProofSharing.c304 := (Enclosure.Real.IsNear.const Bool.false (nat_lit 0) (nat_lit 1))

noncomputable def Gram665ProofSharing.c305 := (@Enclosure.Complex.IsNear.mk Gram665ProofSharing.c256 Gram665ProofSharing.c303 Bool.false (nat_lit 1) (nat_lit 2) (nat_lit 0) (nat_lit 1) Bool.false (nat_lit 0) (nat_lit 1) (nat_lit 0) (nat_lit 1) Gram665ProofSharing.c261 Gram665ProofSharing.c304)

noncomputable def Gram665ProofSharing.c306 := (@Enclosure.Complex.IsNear.of_eq Gram665ProofSharing.c233 { re := Enclosure.sfrac Bool.false (nat_lit 1) (nat_lit 2), im := Enclosure.sfrac Bool.false (nat_lit 0) (nat_lit 1) } Bool.false (nat_lit 1) (nat_lit 2) (nat_lit 0) (nat_lit 1) Bool.false (nat_lit 0) (nat_lit 1) (nat_lit 0) (nat_lit 1) BSN.half_c_mk Gram665ProofSharing.c305)

noncomputable def Gram665ProofSharing.c307 := (@Enclosure.Complex.IsNear.re_isNear Gram665ProofSharing.c233 Bool.false (nat_lit 1) (nat_lit 2) (nat_lit 0) (nat_lit 1) Bool.false (nat_lit 0) (nat_lit 1) (nat_lit 0) (nat_lit 1) Gram665ProofSharing.c306)

noncomputable def Gram665ProofSharing.c308 := (Complex.ofReal_re Gram665ProofSharing.c8)

noncomputable def Gram665ProofSharing.c309 := (@Enclosure.Real.IsNear.of_eq (Gram665ProofSharing.c300 : ℂ).re Gram665ProofSharing.c8 Bool.false (nat_lit 3946810947) (nat_lit 2147483648) (nat_lit 1) (nat_lit 4294967296) Gram665ProofSharing.c308 Zeta.Certificates.Gram.gp11_cert._proof_1)

noncomputable def Gram665ProofSharing.c310 := (@Enclosure.Real.IsNear.mulLit_ff (Gram665ProofSharing.c233 : ℂ).re (Gram665ProofSharing.c300 : ℂ).re (nat_lit 1) (nat_lit 2) (nat_lit 0) (nat_lit 1) (nat_lit 3946810947) (nat_lit 2147483648) (nat_lit 1) (nat_lit 4294967296) (nat_lit 3946810947) (nat_lit 4294967296) (nat_lit 1) (nat_lit 8589934592) Gram665ProofSharing.c307 Gram665ProofSharing.c309 (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram665ProofSharing.c311 := (@Enclosure.Complex.IsNear.im_isNear Gram665ProofSharing.c233 Bool.false (nat_lit 1) (nat_lit 2) (nat_lit 0) (nat_lit 1) Bool.false (nat_lit 0) (nat_lit 1) (nat_lit 0) (nat_lit 1) Gram665ProofSharing.c306)

noncomputable def Gram665ProofSharing.c312 := (Complex.ofReal_im Gram665ProofSharing.c8)

noncomputable def Gram665ProofSharing.c313 := (@Eq.trans.{1} Real (Gram665ProofSharing.c300 : ℂ).im Gram665ProofSharing.c147 Gram665ProofSharing.c303 Gram665ProofSharing.c312 Enclosure.sfrac_zero_eq)

noncomputable def Gram665ProofSharing.c314 := (@Enclosure.Real.IsNear.of_eq (Gram665ProofSharing.c300 : ℂ).im Gram665ProofSharing.c303 Bool.false (nat_lit 0) (nat_lit 1) (nat_lit 0) (nat_lit 1) Gram665ProofSharing.c313 Gram665ProofSharing.c304)

noncomputable def Gram665ProofSharing.c315 := (@Enclosure.Real.IsNear.mulLit_ff (Gram665ProofSharing.c233 : ℂ).im (Gram665ProofSharing.c300 : ℂ).im (nat_lit 0) (nat_lit 1) (nat_lit 0) (nat_lit 1) (nat_lit 0) (nat_lit 1) (nat_lit 0) (nat_lit 1) (nat_lit 0) (nat_lit 1) (nat_lit 0) (nat_lit 1) Gram665ProofSharing.c311 Gram665ProofSharing.c314 (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram665ProofSharing.c316 := (@Enclosure.Real.IsNear.subLit_ff_p Gram665ProofSharing.c301 Gram665ProofSharing.c302 (nat_lit 3946810947) (nat_lit 4294967296) (nat_lit 1) (nat_lit 8589934592) (nat_lit 0) (nat_lit 1) (nat_lit 0) (nat_lit 1) (nat_lit 3946810947) (nat_lit 3946810947) (nat_lit 4294967296) (nat_lit 1) (nat_lit 8589934592) Gram665ProofSharing.c310 Gram665ProofSharing.c315 (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram665ProofSharing.c317 := (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) (Gram665ProofSharing.c233 : ℂ).re (Gram665ProofSharing.c300 : ℂ).im)

noncomputable def Gram665ProofSharing.c318 := (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) (Gram665ProofSharing.c233 : ℂ).im (Gram665ProofSharing.c300 : ℂ).re)

noncomputable def Gram665ProofSharing.c319 := (@Enclosure.Real.IsNear.mulLit_ff (Gram665ProofSharing.c233 : ℂ).re (Gram665ProofSharing.c300 : ℂ).im (nat_lit 1) (nat_lit 2) (nat_lit 0) (nat_lit 1) (nat_lit 0) (nat_lit 1) (nat_lit 0) (nat_lit 1) (nat_lit 0) (nat_lit 1) (nat_lit 0) (nat_lit 1) Gram665ProofSharing.c307 Gram665ProofSharing.c314 (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram665ProofSharing.c320 := (@Enclosure.Real.IsNear.mulLit_ff (Gram665ProofSharing.c233 : ℂ).im (Gram665ProofSharing.c300 : ℂ).re (nat_lit 0) (nat_lit 1) (nat_lit 0) (nat_lit 1) (nat_lit 3946810947) (nat_lit 2147483648) (nat_lit 1) (nat_lit 4294967296) (nat_lit 0) (nat_lit 1) (nat_lit 0) (nat_lit 1) Gram665ProofSharing.c311 Gram665ProofSharing.c309 (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram665ProofSharing.c321 := (@Enclosure.Real.IsNear.addLit_ff Gram665ProofSharing.c317 Gram665ProofSharing.c318 (nat_lit 0) (nat_lit 1) (nat_lit 0) (nat_lit 1) (nat_lit 0) (nat_lit 1) (nat_lit 0) (nat_lit 1) (nat_lit 0) (nat_lit 0) (nat_lit 1) (nat_lit 0) (nat_lit 1) Gram665ProofSharing.c319 Gram665ProofSharing.c320 (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram665ProofSharing.c322 := (@Enclosure.Complex.IsNear.mul Gram665ProofSharing.c233 Gram665ProofSharing.c300 Bool.false (nat_lit 3946810947) (nat_lit 4294967296) (nat_lit 1) (nat_lit 8589934592) Bool.false (nat_lit 0) (nat_lit 1) (nat_lit 0) (nat_lit 1) Gram665ProofSharing.c316 Gram665ProofSharing.c321)

noncomputable def Gram665ProofSharing.c323 := (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) Gram665ProofSharing.c32 (nat_lit 2))

noncomputable def Gram665ProofSharing.c324 := (bernoulli Gram665ProofSharing.c323)

noncomputable def Gram665ProofSharing.c325 := (@Rat.cast.{0} Complex Complex.instRatCast Gram665ProofSharing.c324)

noncomputable def Gram665ProofSharing.c326 := (@Nat.cast.{0} Complex Complex.instNatCast (nat_lit 2))

noncomputable def Gram665ProofSharing.c327 := (@HMul.hMul.{0, 0, 0} Complex Complex Complex (@instHMul.{0} Complex Complex.instMul) Gram665ProofSharing.c42 Gram665ProofSharing.c326)

noncomputable def Gram665ProofSharing.c328 := (@HSub.hSub.{0, 0, 0} Complex Complex Complex (@instHSub.{0} Complex Complex.instSub) Gram665ProofSharing.c327 Gram665ProofSharing.c30)

noncomputable def Gram665ProofSharing.c329 := (@HMul.hMul.{0, 0, 0} Complex Complex Complex (@instHMul.{0} Complex Complex.instMul) Gram665ProofSharing.c327 Gram665ProofSharing.c328)

noncomputable def Gram665ProofSharing.c330 := (@HDiv.hDiv.{0, 0, 0} Complex Complex Complex Gram665ProofSharing.c28 Gram665ProofSharing.c325 Gram665ProofSharing.c329)

noncomputable def Gram665ProofSharing.c331 := (@Nat.cast.{0} Int instNatCastInt (nat_lit 2))

noncomputable def Gram665ProofSharing.c332 := (@HMul.hMul.{0, 0, 0} Int Int Int (@instHMul.{0} Int Int.instMul) Gram665ProofSharing.c244 Gram665ProofSharing.c331)

noncomputable def Gram665ProofSharing.c333 := (@HSub.hSub.{0, 0, 0} Int Int Int (@instHSub.{0} Int Int.instSub) Gram665ProofSharing.c243 Gram665ProofSharing.c332)

noncomputable def Gram665ProofSharing.c334 := (@HPow.hPow.{0, 0, 0} Complex Int Complex Gram665ProofSharing.c242 Gram665ProofSharing.c47 Gram665ProofSharing.c333)

noncomputable def Gram665ProofSharing.c335 := (@HMul.hMul.{0, 0, 0} Complex Complex Complex (@instHMul.{0} Complex Complex.instMul) Gram665ProofSharing.c330 Gram665ProofSharing.c334)

noncomputable def Gram665ProofSharing.c336 := (nat_lit 1980704062856608439838598758400000000000)

noncomputable def Gram665ProofSharing.c337 := (nat_lit 2064728683428660453455440770429693)

noncomputable def Gram665ProofSharing.c338 := (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) Gram665ProofSharing.c32 (nat_lit 1))

noncomputable def Gram665ProofSharing.c339 := (bernoulli Gram665ProofSharing.c338)

noncomputable def Gram665ProofSharing.c340 := (@Rat.cast.{0} Complex Complex.instRatCast Gram665ProofSharing.c339)

noncomputable def Gram665ProofSharing.c341 := (@Nat.cast.{0} Complex Complex.instNatCast (nat_lit 1))

noncomputable def Gram665ProofSharing.c342 := (@HMul.hMul.{0, 0, 0} Complex Complex Complex (@instHMul.{0} Complex Complex.instMul) Gram665ProofSharing.c42 Gram665ProofSharing.c341)

noncomputable def Gram665ProofSharing.c343 := (@HSub.hSub.{0, 0, 0} Complex Complex Complex (@instHSub.{0} Complex Complex.instSub) Gram665ProofSharing.c342 Gram665ProofSharing.c30)

noncomputable def Gram665ProofSharing.c344 := (@HMul.hMul.{0, 0, 0} Complex Complex Complex (@instHMul.{0} Complex Complex.instMul) Gram665ProofSharing.c342 Gram665ProofSharing.c343)

noncomputable def Gram665ProofSharing.c345 := (@HDiv.hDiv.{0, 0, 0} Complex Complex Complex Gram665ProofSharing.c28 Gram665ProofSharing.c340 Gram665ProofSharing.c344)

noncomputable def Gram665ProofSharing.c346 := (@Nat.cast.{0} Int instNatCastInt (nat_lit 1))

noncomputable def Gram665ProofSharing.c347 := (@HMul.hMul.{0, 0, 0} Int Int Int (@instHMul.{0} Int Int.instMul) Gram665ProofSharing.c244 Gram665ProofSharing.c346)

noncomputable def Gram665ProofSharing.c348 := (@HSub.hSub.{0, 0, 0} Int Int Int (@instHSub.{0} Int Int.instSub) Gram665ProofSharing.c243 Gram665ProofSharing.c347)

noncomputable def Gram665ProofSharing.c349 := (@HPow.hPow.{0, 0, 0} Complex Int Complex Gram665ProofSharing.c242 Gram665ProofSharing.c47 Gram665ProofSharing.c348)

noncomputable def Gram665ProofSharing.c350 := (@HMul.hMul.{0, 0, 0} Complex Complex Complex (@instHMul.{0} Complex Complex.instMul) Gram665ProofSharing.c345 Gram665ProofSharing.c349)

noncomputable def Gram665ProofSharing.c351 := (@Enclosure.Complex.IsNear.mk Gram665ProofSharing.c303 Gram665ProofSharing.c303 Bool.false (nat_lit 0) (nat_lit 1) (nat_lit 0) (nat_lit 1) Bool.false (nat_lit 0) (nat_lit 1) (nat_lit 0) (nat_lit 1) Gram665ProofSharing.c304 Gram665ProofSharing.c304)

noncomputable def Gram665ProofSharing.c352 := (BSN.stirling_coeff_mk (nat_lit 1) (nat_lit 1) (nat_lit 6) Bool.false BSN.bern_real_1 (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram665ProofSharing.c353 := (Enclosure.sfrac Bool.false (nat_lit 1) (nat_lit 12))

noncomputable def Gram665ProofSharing.c354 := (Enclosure.Real.IsNear.const Bool.false (nat_lit 1) (nat_lit 12))

noncomputable def Gram665ProofSharing.c355 := (@Enclosure.Complex.IsNear.mk Gram665ProofSharing.c353 Gram665ProofSharing.c303 Bool.false (nat_lit 1) (nat_lit 12) (nat_lit 0) (nat_lit 1) Bool.false (nat_lit 0) (nat_lit 1) (nat_lit 0) (nat_lit 1) Gram665ProofSharing.c354 Gram665ProofSharing.c304)

noncomputable def Gram665ProofSharing.c356 := (@Enclosure.Complex.IsNear.of_eq Gram665ProofSharing.c345 { re := Enclosure.sfrac Bool.false (nat_lit 1) (nat_lit 12), im := Enclosure.sfrac Bool.false (nat_lit 0) (nat_lit 1) } Bool.false (nat_lit 1) (nat_lit 12) (nat_lit 0) (nat_lit 1) Bool.false (nat_lit 0) (nat_lit 1) (nat_lit 0) (nat_lit 1) Gram665ProofSharing.c352 Gram665ProofSharing.c355)

noncomputable def Gram665ProofSharing.c357 := (@Enclosure.Complex.IsNear.re_isNear Gram665ProofSharing.c345 Bool.false (nat_lit 1) (nat_lit 12) (nat_lit 0) (nat_lit 1) Bool.false (nat_lit 0) (nat_lit 1) (nat_lit 0) (nat_lit 1) Gram665ProofSharing.c356)

noncomputable def Gram665ProofSharing.c358 := (@Inv.inv.{0} Complex Complex.instInv Gram665ProofSharing.c50)

noncomputable def Gram665ProofSharing.c359 := (BSN.zpow_one_sub_two_mul Gram665ProofSharing.c47 (nat_lit 1) (nat_lit 1) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram665ProofSharing.c360 := (@instMulZeroOneClassOfSemiring.{0} Complex Complex.instSemiring)

noncomputable def Gram665ProofSharing.c361 := (@instMulZeroOneClassOfSemiring.{0} Real Real.semiring)

noncomputable def Gram665ProofSharing.c362 := (@MonoidWithZeroHom.{0, 0} Complex Real Gram665ProofSharing.c360 Gram665ProofSharing.c361)

noncomputable def Gram665ProofSharing.c363 := (@MonoidWithZeroHom.funLike.{0, 0} Complex Real Gram665ProofSharing.c360 Gram665ProofSharing.c361)

noncomputable def Gram665ProofSharing.c364 := (Enclosure.Complex.inv_re_eq_mul Gram665ProofSharing.c50)

noncomputable def Gram665ProofSharing.c365 := (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) (Gram665ProofSharing.c50 : ℂ).re (Gram665ProofSharing.c50 : ℂ).re)

noncomputable def Gram665ProofSharing.c366 := (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) (Gram665ProofSharing.c50 : ℂ).im (Gram665ProofSharing.c50 : ℂ).im)

noncomputable def Gram665ProofSharing.c367 := (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd) Gram665ProofSharing.c365 Gram665ProofSharing.c366)

noncomputable def Gram665ProofSharing.c368 := (Enclosure.Complex.normSq_eq_mul_add_mul Gram665ProofSharing.c50)

noncomputable def Gram665ProofSharing.c369 := (@Enclosure.Real.IsNear.mulLit_ff (Gram665ProofSharing.c50 : ℂ).re (Gram665ProofSharing.c50 : ℂ).re (nat_lit 100000) (nat_lit 400000) (nat_lit 0) (nat_lit 1) (nat_lit 100000) (nat_lit 400000) (nat_lit 0) (nat_lit 1) (nat_lit 1) (nat_lit 16) (nat_lit 0) (nat_lit 1) Gram665ProofSharing.c65 Gram665ProofSharing.c65 (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram665ProofSharing.c370 := (@Enclosure.Real.IsNear.mulLit_ff (Gram665ProofSharing.c50 : ℂ).im (Gram665ProofSharing.c50 : ℂ).im (nat_lit 204299742) (nat_lit 400000) (nat_lit 0) (nat_lit 1) (nat_lit 204299742) (nat_lit 400000) (nat_lit 0) (nat_lit 1) (nat_lit 10434596145316641) (nat_lit 40000000000) (nat_lit 0) (nat_lit 1) Gram665ProofSharing.c68 Gram665ProofSharing.c68 (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram665ProofSharing.c371 := (@Enclosure.Real.IsNear.addLit_ff Gram665ProofSharing.c365 Gram665ProofSharing.c366 (nat_lit 1) (nat_lit 16) (nat_lit 0) (nat_lit 1) (nat_lit 10434596145316641) (nat_lit 40000000000) (nat_lit 0) (nat_lit 1) (nat_lit 166953578325066256) (nat_lit 10434598645316641) (nat_lit 40000000000) (nat_lit 0) (nat_lit 1) Gram665ProofSharing.c369 Gram665ProofSharing.c370 (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram665ProofSharing.c372 := (@Neg.neg.{0} Real Real.instNeg (Gram665ProofSharing.c50 : ℂ).im)

noncomputable def Gram665ProofSharing.c373 := (Enclosure.Complex.inv_im_eq_mul Gram665ProofSharing.c50)

noncomputable def Gram665ProofSharing.c374 := (@Enclosure.Real.IsNear.neg (Gram665ProofSharing.c50 : ℂ).im Bool.false (nat_lit 204299742) (nat_lit 400000) (nat_lit 0) (nat_lit 1) Gram665ProofSharing.c68)

noncomputable def Gram665ProofSharing.c375 := (@Enclosure.Complex.IsNear.im_isNear Gram665ProofSharing.c345 Bool.false (nat_lit 1) (nat_lit 12) (nat_lit 0) (nat_lit 1) Bool.false (nat_lit 0) (nat_lit 1) (nat_lit 0) (nat_lit 1) Gram665ProofSharing.c356)

noncomputable def Gram665ProofSharing.c376 := (nat_lit 49517601571415210995964968960000000000)

noncomputable def Gram665ProofSharing.c377 := (BSN.stirling_coeff_mk (nat_lit 2) (nat_lit 1) (nat_lit 30) Bool.true BSN.bern_real_2 (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram665ProofSharing.c378 := (Enclosure.sfrac Bool.true (nat_lit 1) (nat_lit 360))

noncomputable def Gram665ProofSharing.c379 := (Enclosure.Real.IsNear.const Bool.true (nat_lit 1) (nat_lit 360))

noncomputable def Gram665ProofSharing.c380 := (@Enclosure.Complex.IsNear.mk Gram665ProofSharing.c378 Gram665ProofSharing.c303 Bool.true (nat_lit 1) (nat_lit 360) (nat_lit 0) (nat_lit 1) Bool.false (nat_lit 0) (nat_lit 1) (nat_lit 0) (nat_lit 1) Gram665ProofSharing.c379 Gram665ProofSharing.c304)

noncomputable def Gram665ProofSharing.c381 := (@Enclosure.Complex.IsNear.of_eq Gram665ProofSharing.c330 { re := Enclosure.sfrac Bool.true (nat_lit 1) (nat_lit 360), im := Enclosure.sfrac Bool.false (nat_lit 0) (nat_lit 1) } Bool.true (nat_lit 1) (nat_lit 360) (nat_lit 0) (nat_lit 1) Bool.false (nat_lit 0) (nat_lit 1) (nat_lit 0) (nat_lit 1) Gram665ProofSharing.c377 Gram665ProofSharing.c380)

noncomputable def Gram665ProofSharing.c382 := (@Enclosure.Complex.IsNear.re_isNear Gram665ProofSharing.c330 Bool.true (nat_lit 1) (nat_lit 360) (nat_lit 0) (nat_lit 1) Bool.false (nat_lit 0) (nat_lit 1) (nat_lit 0) (nat_lit 1) Gram665ProofSharing.c381)

noncomputable def Gram665ProofSharing.c383 := (nat_lit 18582558150857944081098966933867237)

noncomputable def Gram665ProofSharing.c384 := (nat_lit 2475880078570760549798248448000000000000000)

noncomputable def Gram665ProofSharing.c385 := (@Inv.inv.{0} Complex Complex.instInv Gram665ProofSharing.c48)

noncomputable def Gram665ProofSharing.c386 := (BSN.zpow_one_sub_two_mul Gram665ProofSharing.c47 (nat_lit 2) (nat_lit 3) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram665ProofSharing.c387 := (Enclosure.Complex.inv_re_eq_mul Gram665ProofSharing.c48)

noncomputable def Gram665ProofSharing.c388 := (@Enclosure.Complex.IsNear.re_isNear Gram665ProofSharing.c48 Bool.true (nat_lit 31303785935949923) (nat_lit 160000000000) (nat_lit 0) (nat_lit 1) Bool.true (nat_lit 1065891884057159632303311) (nat_lit 8000000000000000) (nat_lit 0) (nat_lit 1) Zeta.Certificates.Gram.gp11_cert._proof_2)

noncomputable def Gram665ProofSharing.c389 := (nat_lit 1136127958316456241772805864441806979197601562721)

noncomputable def Gram665ProofSharing.c390 := (nat_lit 64000000000000000000000000000000)

noncomputable def Gram665ProofSharing.c391 := (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) (Gram665ProofSharing.c48 : ℂ).re (Gram665ProofSharing.c48 : ℂ).re)

noncomputable def Gram665ProofSharing.c392 := (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) (Gram665ProofSharing.c48 : ℂ).im (Gram665ProofSharing.c48 : ℂ).im)

noncomputable def Gram665ProofSharing.c393 := (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd) Gram665ProofSharing.c391 Gram665ProofSharing.c392)

noncomputable def Gram665ProofSharing.c394 := (Enclosure.Complex.normSq_eq_mul_add_mul Gram665ProofSharing.c48)

noncomputable def Gram665ProofSharing.c395 := (nat_lit 979927013923776196719368363705929)

noncomputable def Gram665ProofSharing.c396 := (nat_lit 1136125508498921432332314066020897714375101562721)

noncomputable def Gram665ProofSharing.c397 := (nat_lit 29084875732901279789383830129710258667458600005657600000000000000000000)

noncomputable def Gram665ProofSharing.c398 := (@Enclosure.Real.IsNear.mulLit_tt (Gram665ProofSharing.c48 : ℂ).re (Gram665ProofSharing.c48 : ℂ).re (nat_lit 31303785935949923) (nat_lit 160000000000) (nat_lit 0) (nat_lit 1) (nat_lit 31303785935949923) (nat_lit 160000000000) (nat_lit 0) (nat_lit 1) Gram665ProofSharing.c395 (nat_lit 25600000000000000000000) (nat_lit 0) (nat_lit 1) Gram665ProofSharing.c388 Gram665ProofSharing.c388 (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram665ProofSharing.c399 := (@Enclosure.Complex.IsNear.im_isNear Gram665ProofSharing.c48 Bool.true (nat_lit 31303785935949923) (nat_lit 160000000000) (nat_lit 0) (nat_lit 1) Bool.true (nat_lit 1065891884057159632303311) (nat_lit 8000000000000000) (nat_lit 0) (nat_lit 1) Zeta.Certificates.Gram.gp11_cert._proof_2)

noncomputable def Gram665ProofSharing.c400 := (@Enclosure.Real.IsNear.mulLit_tt (Gram665ProofSharing.c48 : ℂ).im (Gram665ProofSharing.c48 : ℂ).im (nat_lit 1065891884057159632303311) (nat_lit 8000000000000000) (nat_lit 0) (nat_lit 1) (nat_lit 1065891884057159632303311) (nat_lit 8000000000000000) (nat_lit 0) (nat_lit 1) Gram665ProofSharing.c396 Gram665ProofSharing.c390 (nat_lit 0) (nat_lit 1) Gram665ProofSharing.c399 Gram665ProofSharing.c399 (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram665ProofSharing.c401 := (@Enclosure.Real.IsNear.addLit_ff Gram665ProofSharing.c391 Gram665ProofSharing.c392 Gram665ProofSharing.c395 (nat_lit 25600000000000000000000) (nat_lit 0) (nat_lit 1) Gram665ProofSharing.c396 Gram665ProofSharing.c390 (nat_lit 0) (nat_lit 1) Gram665ProofSharing.c397 Gram665ProofSharing.c389 Gram665ProofSharing.c390 (nat_lit 0) (nat_lit 1) Gram665ProofSharing.c398 Gram665ProofSharing.c400 (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram665ProofSharing.c402 := (@Neg.neg.{0} Real Real.instNeg (Gram665ProofSharing.c48 : ℂ).im)

noncomputable def Gram665ProofSharing.c403 := (Enclosure.Complex.inv_im_eq_mul Gram665ProofSharing.c48)

noncomputable def Gram665ProofSharing.c404 := (@Enclosure.Real.IsNear.neg (Gram665ProofSharing.c48 : ℂ).im Bool.true (nat_lit 1065891884057159632303311) (nat_lit 8000000000000000) (nat_lit 0) (nat_lit 1) Gram665ProofSharing.c399)

noncomputable def Gram665ProofSharing.c405 := (@Enclosure.Complex.IsNear.im_isNear Gram665ProofSharing.c330 Bool.true (nat_lit 1) (nat_lit 360) (nat_lit 0) (nat_lit 1) Bool.false (nat_lit 0) (nat_lit 1) (nat_lit 0) (nat_lit 1) Gram665ProofSharing.c381)

noncomputable def Gram665ProofSharing.c406 := (BSN.logSumC Gram665ProofSharing.c39 (nat_lit 0))

noncomputable def Gram665ProofSharing.c407 := (Enclosure.sfrac Bool.false (nat_lit 98304000000000000000000000) Gram665ProofSharing.c106)

noncomputable def Gram665ProofSharing.c408 := (@Monoid.toNPow.{0} Real Real.instMonoid)

noncomputable def Gram665ProofSharing.c409 := (@NPow.toPow.{0} Real Gram665ProofSharing.c408)

noncomputable def Gram665ProofSharing.c410 := (@instHPow.{0, 0} Real Nat Gram665ProofSharing.c409)

noncomputable def Gram665ProofSharing.c411 := (@HPow.hPow.{0, 0, 0} Real Nat Real Gram665ProofSharing.c410 Gram665ProofSharing.c7 (nat_lit 4))

noncomputable def Gram665ProofSharing.c412 := (@Inv.inv.{0} Real Real.instInv Gram665ProofSharing.c411)

noncomputable def Gram665ProofSharing.c413 := (nat_lit 611446774371975769155682509262542103857872115376664175900625)

noncomputable def Gram665ProofSharing.c414 := (nat_lit 392318858461667547739736838950479151006397215279002157056)

noncomputable def Gram665ProofSharing.c415 := (nat_lit 19652562622312316682495810535216024035134795670488584765154486969712234385047)

noncomputable def Gram665ProofSharing.c416 := (nat_lit 9903520314283042199192993792000000000000000000000000000000000000000000000000000000000000)

noncomputable def Gram665ProofSharing.c417 := (@HPow.hPow.{0, 0, 0} Real Nat Real Gram665ProofSharing.c410 Gram665ProofSharing.c7 (nat_lit 3))

noncomputable def Gram665ProofSharing.c418 := (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) Gram665ProofSharing.c417 Gram665ProofSharing.c7)

noncomputable def Gram665ProofSharing.c419 := (BSN.pow_succ_r Gram665ProofSharing.c7 (nat_lit 3) (nat_lit 4) (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram665ProofSharing.c420 := (nat_lit 691463075802508163054686763366652189853178875)

noncomputable def Gram665ProofSharing.c421 := (nat_lit 2787593149816327892691964784081045188247552)

noncomputable def Gram665ProofSharing.c422 := (nat_lit 2184744797947834540264818678394244808492865883128339)

noncomputable def Gram665ProofSharing.c423 := (nat_lit 9223372036854775808000000000000000000000000000000000000000000000)

noncomputable def Gram665ProofSharing.c424 := (@HPow.hPow.{0, 0, 0} Real Nat Real Gram665ProofSharing.c410 Gram665ProofSharing.c7 (nat_lit 2))

noncomputable def Gram665ProofSharing.c425 := (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) Gram665ProofSharing.c424 Gram665ProofSharing.c7)

noncomputable def Gram665ProofSharing.c426 := (BSN.pow_succ_r Gram665ProofSharing.c7 (nat_lit 2) (nat_lit 3) (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram665ProofSharing.c427 := (nat_lit 1073741824000000000000000000000000000000)

noncomputable def Gram665ProofSharing.c428 := (@HPow.hPow.{0, 0, 0} Real Nat Real Gram665ProofSharing.c410 Gram665ProofSharing.c7 (nat_lit 1))

noncomputable def Gram665ProofSharing.c429 := (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) Gram665ProofSharing.c428 Gram665ProofSharing.c7)

noncomputable def Gram665ProofSharing.c430 := (BSN.pow_succ_r Gram665ProofSharing.c7 (nat_lit 1) (nat_lit 2) (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram665ProofSharing.c431 := (BSN.pow_one_r Gram665ProofSharing.c7)

noncomputable def Gram665ProofSharing.c432 := (@Enclosure.Real.IsNear.of_eq Gram665ProofSharing.c7 Gram665ProofSharing.c10 Bool.false (nat_lit 884279719003555) (nat_lit 140737488355328) (nat_lit 1) (nat_lit 500000000000000) BSN.two_pi_eq Gram665ProofSharing.c13)

noncomputable def Gram665ProofSharing.c433 := (@Enclosure.Real.IsNear.of_eq Gram665ProofSharing.c428 Gram665ProofSharing.c7 Bool.false (nat_lit 884279719003555) (nat_lit 140737488355328) (nat_lit 1) (nat_lit 500000000000000) Gram665ProofSharing.c431 Gram665ProofSharing.c432)

noncomputable def Gram665ProofSharing.c434 := (@Enclosure.Real.IsNear.mulLit_ff Gram665ProofSharing.c428 Gram665ProofSharing.c7 (nat_lit 884279719003555) (nat_lit 140737488355328) (nat_lit 1) (nat_lit 500000000000000) (nat_lit 884279719003555) (nat_lit 140737488355328) (nat_lit 1) (nat_lit 500000000000000) (nat_lit 781950621441006189802102638025) (nat_lit 19807040628566084398385987584) (nat_lit 26986075409044041160201671) Gram665ProofSharing.c427 Gram665ProofSharing.c433 Gram665ProofSharing.c432 (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram665ProofSharing.c435 := (@Enclosure.Real.IsNear.of_eq Gram665ProofSharing.c424 Gram665ProofSharing.c429 Bool.false (nat_lit 781950621441006189802102638025) (nat_lit 19807040628566084398385987584) (nat_lit 26986075409044041160201671) Gram665ProofSharing.c427 Gram665ProofSharing.c430 Gram665ProofSharing.c434)

noncomputable def Gram665ProofSharing.c436 := (@Enclosure.Real.IsNear.mulLit_ff Gram665ProofSharing.c424 Gram665ProofSharing.c7 (nat_lit 781950621441006189802102638025) (nat_lit 19807040628566084398385987584) (nat_lit 26986075409044041160201671) Gram665ProofSharing.c427 (nat_lit 884279719003555) (nat_lit 140737488355328) (nat_lit 1) (nat_lit 500000000000000) Gram665ProofSharing.c420 Gram665ProofSharing.c421 Gram665ProofSharing.c422 Gram665ProofSharing.c423 Gram665ProofSharing.c435 Gram665ProofSharing.c432 (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram665ProofSharing.c437 := (@Enclosure.Real.IsNear.of_eq Gram665ProofSharing.c417 Gram665ProofSharing.c425 Bool.false Gram665ProofSharing.c420 Gram665ProofSharing.c421 Gram665ProofSharing.c422 Gram665ProofSharing.c423 Gram665ProofSharing.c426 Gram665ProofSharing.c436)

noncomputable def Gram665ProofSharing.c438 := (@Enclosure.Real.IsNear.mulLit_ff Gram665ProofSharing.c417 Gram665ProofSharing.c7 Gram665ProofSharing.c420 Gram665ProofSharing.c421 Gram665ProofSharing.c422 Gram665ProofSharing.c423 (nat_lit 884279719003555) (nat_lit 140737488355328) (nat_lit 1) (nat_lit 500000000000000) Gram665ProofSharing.c413 Gram665ProofSharing.c414 Gram665ProofSharing.c415 Gram665ProofSharing.c416 Gram665ProofSharing.c437 Gram665ProofSharing.c432 (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram665ProofSharing.c439 := (@Enclosure.Real.IsNear.of_eq Gram665ProofSharing.c411 Gram665ProofSharing.c418 Bool.false Gram665ProofSharing.c413 Gram665ProofSharing.c414 Gram665ProofSharing.c415 Gram665ProofSharing.c416 Gram665ProofSharing.c419 Gram665ProofSharing.c438)

noncomputable def Gram665ProofSharing.c440 := (@Enclosure.Real.IsNear.inv_image Gram665ProofSharing.c411 Gram665ProofSharing.c413 Gram665ProofSharing.c414 Gram665ProofSharing.c415 Gram665ProofSharing.c416 (nat_lit 5511507) (nat_lit 5511508) (nat_lit 8589934592) Gram665ProofSharing.c439 (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram665ProofSharing.c441 := (@Enclosure.Real.IsNear.recentre' Gram665ProofSharing.c412 Bool.false (nat_lit 11023015) (nat_lit 17179869184) (nat_lit 1) (nat_lit 17179869184) (nat_lit 11023015) (nat_lit 17179869184) (nat_lit 1) (nat_lit 17179869184) Gram665ProofSharing.c440 (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram665ProofSharing.c442 := (nat_lit 97716337700145345607713650232933952657)

noncomputable def Gram665ProofSharing.c443 := (nat_lit 20586592834600762896784348726870211544801)

noncomputable def Gram665ProofSharing.c444 := (nat_lit 131531129174071654208031948800000000000000000000)

noncomputable def Gram665ProofSharing.c445 := (nat_lit 1742093786872948954606185895158016)

noncomputable def Gram665ProofSharing.c446 := (riemannSiegelThetaApproximant (nat_lit 2) (nat_lit 0) Gram665ProofSharing.c107)

noncomputable def Gram665ProofSharing.c447 := (nat_lit 5172507530611139738458901985313650232933952657)

noncomputable def Gram665ProofSharing.c448 := (nat_lit 20586505366399862139134300385624259544801)

noncomputable def Gram665ProofSharing.c449 := (Complex.Stirling.logGammaStirling (nat_lit 2) Gram665ProofSharing.c112)

noncomputable def Gram665ProofSharing.c450 := (@HDiv.hDiv.{0, 0, 0} Real Real Real Gram665ProofSharing.c15 Gram665ProofSharing.c107 Gram665ProofSharing.c6)

noncomputable def Gram665ProofSharing.c451 := (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) Gram665ProofSharing.c450 (Real.log Real.pi))

noncomputable def Gram665ProofSharing.c452 := (nat_lit 6620080504412468269804161723294250552933952657)

noncomputable def Gram665ProofSharing.c453 := (nat_lit 4945072794000196136739164385624259544801)

noncomputable def Gram665ProofSharing.c454 := (nat_lit 238553006126698540189734316021393591846049)

noncomputable def Gram665ProofSharing.c455 := (nat_lit 297105609428491265975789813760000000000)

noncomputable def Gram665ProofSharing.c456 := (nat_lit 11134230268639005893236638144533612537519)

noncomputable def Gram665ProofSharing.c457 := (nat_lit 147972520320830610984035942400000000000000000000)

noncomputable def Gram665ProofSharing.c458 := (@HSub.hSub.{0, 0, 0} Complex Complex Complex (@instHSub.{0} Complex Complex.instSub) Gram665ProofSharing.c112 Gram665ProofSharing.c233)

noncomputable def Gram665ProofSharing.c459 := (Complex.log Gram665ProofSharing.c112)

noncomputable def Gram665ProofSharing.c460 := (@HMul.hMul.{0, 0, 0} Complex Complex Complex (@instHMul.{0} Complex Complex.instMul) Gram665ProofSharing.c458 Gram665ProofSharing.c459)

noncomputable def Gram665ProofSharing.c461 := (@HSub.hSub.{0, 0, 0} Complex Complex Complex (@instHSub.{0} Complex Complex.instSub) Gram665ProofSharing.c460 Gram665ProofSharing.c112)

noncomputable def Gram665ProofSharing.c462 := (@HAdd.hAdd.{0, 0, 0} Complex Complex Complex (@instHAdd.{0} Complex Complex.instAdd) Gram665ProofSharing.c461 Gram665ProofSharing.c238)

noncomputable def Gram665ProofSharing.c463 := (nat_lit 23727610102299149879623086553951)

noncomputable def Gram665ProofSharing.c464 := (nat_lit 4456584141427368989636847206400000000000)

noncomputable def Gram665ProofSharing.c465 := (nat_lit 403961960475306865730714110407066047343)

noncomputable def Gram665ProofSharing.c466 := (nat_lit 12379400392853802748991242240000000000000000)

noncomputable def Gram665ProofSharing.c467 := (BSN.w_sub_half_zero_mk Gram665ProofSharing.c107 Bool.false (nat_lit 102149874) (nat_lit 100000) Gram665ProofSharing.c121 (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram665ProofSharing.c468 := (@Enclosure.Complex.IsNear.mk Gram665ProofSharing.c249 Gram665ProofSharing.c123 Bool.true (nat_lit 100000) (nat_lit 400000) (nat_lit 0) (nat_lit 1) Bool.false (nat_lit 204299748) (nat_lit 400000) (nat_lit 0) (nat_lit 1) Gram665ProofSharing.c250 Gram665ProofSharing.c124)

noncomputable def Gram665ProofSharing.c469 := (@Enclosure.Complex.IsNear.of_eq Gram665ProofSharing.c458 { re := Enclosure.sfrac Bool.true (nat_lit 100000) (nat_lit 400000), im := Enclosure.sfrac Bool.false (nat_lit 204299748) (nat_lit 400000) } Bool.true (nat_lit 100000) (nat_lit 400000) (nat_lit 0) (nat_lit 1) Bool.false (nat_lit 204299748) (nat_lit 400000) (nat_lit 0) (nat_lit 1) Gram665ProofSharing.c467 Gram665ProofSharing.c468)

noncomputable def Gram665ProofSharing.c470 := (@Enclosure.Complex.IsNear.re_isNear Gram665ProofSharing.c458 Bool.true (nat_lit 100000) (nat_lit 400000) (nat_lit 0) (nat_lit 1) Bool.false (nat_lit 204299748) (nat_lit 400000) (nat_lit 0) (nat_lit 1) Gram665ProofSharing.c469)

noncomputable def Gram665ProofSharing.c471 := (Complex.log { re := Enclosure.sfrac Bool.false (nat_lit 100000) (nat_lit 400000), im := Enclosure.sfrac Bool.false (nat_lit 204299748) (nat_lit 400000) })

noncomputable def Gram665ProofSharing.c472 := (@congrArg.{1, 1} Complex Complex Gram665ProofSharing.c112 { re := Enclosure.sfrac Bool.false (nat_lit 100000) (nat_lit 400000), im := Enclosure.sfrac Bool.false (nat_lit 204299748) (nat_lit 400000) } Complex.log Gram665ProofSharing.c122)

noncomputable def Gram665ProofSharing.c473 := (Enclosure.sfrac Bool.false (nat_lit 41738397032863504) (nat_lit 160000000000))

noncomputable def Gram665ProofSharing.c474 := (Real.log Gram665ProofSharing.c473)

noncomputable def Gram665ProofSharing.c475 := (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) Gram665ProofSharing.c256 Gram665ProofSharing.c474)

noncomputable def Gram665ProofSharing.c476 := (Enclosure.clog_re_eq (nat_lit 100000) (nat_lit 204299748) (nat_lit 400000) (nat_lit 41738397032863504) (nat_lit 160000000000) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram665ProofSharing.c477 := (@Nat.cast.{0} Real Real.instNatCast (nat_lit 41738397032863504))

noncomputable def Gram665ProofSharing.c478 := (@HDiv.hDiv.{0, 0, 0} Real Real Real Gram665ProofSharing.c15 Gram665ProofSharing.c477 Gram665ProofSharing.c263)

noncomputable def Gram665ProofSharing.c479 := (Real.log Gram665ProofSharing.c478)

noncomputable def Gram665ProofSharing.c480 := (nat_lit 12162012513207393392282470806862050509196698687967404379606532827908821117298529482657455929829551643240460420799776245061927074508373817138586667780259860452848409260806535843808384574281749430513135753597532149778139622876193778945054022639938303057384241178037680981089656714014013941736450284218828703894649748728285489788991470663359476531200)

noncomputable def Gram665ProofSharing.c481 := (nat_lit 476343903838592859234612061660246395089667449158362467048419546888531512853939767553577882881425111008421652432464052967744525774212344900213373028073239837899744649020875073509220494710559430103875901004171011776742025390954477048083851520348618372624533000573516508848493891405245961103671970928486914849728248556537267012329879164871319224320)

noncomputable def Gram665ProofSharing.c482 := (nat_lit 145708690014352582124942822058148158645782777025047652268803597833582403280480639547168962281396773184522807443051652919048081874381834067155140366501225073844894793082089199998499341318454162549603323818676625726341558683846268393956200160838030444379115690244399193917897171392439242935667746296891512024460794964743910305874260787200)

noncomputable def Gram665ProofSharing.c483 := (BSN.artanhP (nat_lit 20766877032863504))

noncomputable def Gram665ProofSharing.c484 := (BSN.artanhQ (nat_lit 62709917032863504))

noncomputable def Gram665ProofSharing.c485 := (@BSN.binarySplit_of_base10 Gram665ProofSharing.c483 Gram665ProofSharing.c484 (nat_lit 0) (nat_lit 10) Gram665ProofSharing.c481 Gram665ProofSharing.c480 Gram665ProofSharing.c482 (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram665ProofSharing.c486 := (BSN.log_dyadic_bound (nat_lit 20766877032863504) (nat_lit 62709917032863504) (nat_lit 11) (nat_lit 10) Gram665ProofSharing.c480 (nat_lit 17179869184) (nat_lit 6800000000) Gram665ProofSharing.c481 Gram665ProofSharing.c482 (nat_lit 11824150974) (nat_lit 83476794065727008) (nat_lit 41943040000000000) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) Gram665ProofSharing.c485 (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram665ProofSharing.c487 := (BSN.log_rat_reduce_isNear (nat_lit 41738397032863504) (nat_lit 160000000000) (nat_lit 17) (nat_lit 83476794065727008) (nat_lit 41943040000000000) (nat_lit 11824150974) (nat_lit 17179869184) (nat_lit 24973259072661432) (nat_lit 36028797018963968) (nat_lit 6800000000) (nat_lit 1000000000000000) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) Gram665ProofSharing.c486 BSN.log2_near_15 (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram665ProofSharing.c488 := (@Enclosure.Real.IsNear.recentre' Gram665ProofSharing.c479 Bool.false (nat_lit 7719644442793728490894000128) (nat_lit 618970019642690137449562112) (nat_lit 1000115600000000) (nat_lit 6800000000000000000000000) (nat_lit 56167805762333799) (nat_lit 4503599627370496) (nat_lit 2500289) (nat_lit 17000000000000000) Gram665ProofSharing.c487 (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram665ProofSharing.c489 := (BSN.isNear_log_sfrac (nat_lit 41738397032863504) (nat_lit 160000000000) (nat_lit 56167805762333799) (nat_lit 4503599627370496) (nat_lit 2500289) (nat_lit 17000000000000000) Bool.false Gram665ProofSharing.c488)

noncomputable def Gram665ProofSharing.c490 := (@Enclosure.Real.IsNear.mulLit_ff Gram665ProofSharing.c256 Gram665ProofSharing.c474 (nat_lit 1) (nat_lit 2) (nat_lit 0) (nat_lit 1) (nat_lit 56167805762333799) (nat_lit 4503599627370496) (nat_lit 2500289) (nat_lit 17000000000000000) (nat_lit 56167805762333799) (nat_lit 9007199254740992) (nat_lit 2500289) (nat_lit 34000000000000000) Gram665ProofSharing.c261 Gram665ProofSharing.c489 (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram665ProofSharing.c491 := (@Enclosure.Real.IsNear.of_eq (Gram665ProofSharing.c471 : ℂ).re Gram665ProofSharing.c475 Bool.false (nat_lit 56167805762333799) (nat_lit 9007199254740992) (nat_lit 2500289) (nat_lit 34000000000000000) Gram665ProofSharing.c476 Gram665ProofSharing.c490)

noncomputable def Gram665ProofSharing.c492 := (@Nat.cast.{0} Real Real.instNatCast (nat_lit 204299748))

noncomputable def Gram665ProofSharing.c493 := (@HDiv.hDiv.{0, 0, 0} Real Real Real Gram665ProofSharing.c15 Gram665ProofSharing.c492 Gram665ProofSharing.c279)

noncomputable def Gram665ProofSharing.c494 := (Real.arctan Gram665ProofSharing.c493)

noncomputable def Gram665ProofSharing.c495 := (Enclosure.clog_im_eq (nat_lit 100000) (nat_lit 204299748) (nat_lit 400000) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram665ProofSharing.c496 := (@HDiv.hDiv.{0, 0, 0} Real Real Real Gram665ProofSharing.c15 Gram665ProofSharing.c279 Gram665ProofSharing.c492)

noncomputable def Gram665ProofSharing.c497 := (Real.arctan Gram665ProofSharing.c496)

noncomputable def Gram665ProofSharing.c498 := (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) Gram665ProofSharing.c283 Gram665ProofSharing.c497)

noncomputable def Gram665ProofSharing.c499 := (BSN.arctan_recip (nat_lit 204299748) (nat_lit 100000) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram665ProofSharing.c500 := (@BSN.binarySplit_of_le (BSN.arctanEvenP (nat_lit 100000)) (BSN.arctanEvenQ (nat_lit 204299748)) (nat_lit 0) (nat_lit 0) (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram665ProofSharing.c501 := (@BSN.binarySplit_of_le (BSN.arctanOddP (nat_lit 100000)) (BSN.arctanOddQ (nat_lit 204299748)) (nat_lit 0) (nat_lit 0) (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram665ProofSharing.c502 := (BSN.arctan_dyadic_bound_f (nat_lit 100000) (nat_lit 204299748) (nat_lit 1) (nat_lit 0) (nat_lit 17179869184) (nat_lit 6800000000) (nat_lit 0) (nat_lit 1) (nat_lit 1) (nat_lit 0) (nat_lit 1) (nat_lit 1) (nat_lit 8409147) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) Gram665ProofSharing.c500 Gram665ProofSharing.c501 (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram665ProofSharing.c503 := (@Enclosure.Real.IsNear.subLit_ff_p Gram665ProofSharing.c283 Gram665ProofSharing.c497 (nat_lit 884279719003555) (nat_lit 562949953421312) (nat_lit 1) (nat_lit 2000000000000000) (nat_lit 8409147) (nat_lit 17179869184) (nat_lit 1) (nat_lit 6800000000) (nat_lit 15187075965633390765408256) (nat_lit 884004168074659) (nat_lit 562949953421312) (nat_lit 5000017) (nat_lit 34000000000000000) Gram665ProofSharing.c288 Gram665ProofSharing.c502 (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram665ProofSharing.c504 := (@Enclosure.Real.IsNear.of_eq Gram665ProofSharing.c494 Gram665ProofSharing.c498 Bool.false (nat_lit 884004168074659) (nat_lit 562949953421312) (nat_lit 5000017) (nat_lit 34000000000000000) Gram665ProofSharing.c499 Gram665ProofSharing.c503)

noncomputable def Gram665ProofSharing.c505 := (@Enclosure.Real.IsNear.of_eq (Gram665ProofSharing.c471 : ℂ).im Gram665ProofSharing.c494 Bool.false (nat_lit 884004168074659) (nat_lit 562949953421312) (nat_lit 5000017) (nat_lit 34000000000000000) Gram665ProofSharing.c495 Gram665ProofSharing.c504)

noncomputable def Gram665ProofSharing.c506 := (@Enclosure.Complex.IsNear.of_parts Gram665ProofSharing.c471 Bool.false (nat_lit 56167805762333799) (nat_lit 9007199254740992) (nat_lit 2500289) (nat_lit 34000000000000000) Bool.false (nat_lit 884004168074659) (nat_lit 562949953421312) (nat_lit 5000017) (nat_lit 34000000000000000) Gram665ProofSharing.c491 Gram665ProofSharing.c505)

noncomputable def Gram665ProofSharing.c507 := (@Enclosure.Complex.IsNear.of_eq Gram665ProofSharing.c459 Gram665ProofSharing.c471 Bool.false (nat_lit 56167805762333799) (nat_lit 9007199254740992) (nat_lit 2500289) (nat_lit 34000000000000000) Bool.false (nat_lit 884004168074659) (nat_lit 562949953421312) (nat_lit 5000017) (nat_lit 34000000000000000) Gram665ProofSharing.c472 Gram665ProofSharing.c506)

noncomputable def Gram665ProofSharing.c508 := (@Enclosure.Complex.IsNear.re_isNear Gram665ProofSharing.c459 Bool.false (nat_lit 56167805762333799) (nat_lit 9007199254740992) (nat_lit 2500289) (nat_lit 34000000000000000) Bool.false (nat_lit 884004168074659) (nat_lit 562949953421312) (nat_lit 5000017) (nat_lit 34000000000000000) Gram665ProofSharing.c507)

noncomputable def Gram665ProofSharing.c509 := (@Enclosure.Complex.IsNear.im_isNear Gram665ProofSharing.c458 Bool.true (nat_lit 100000) (nat_lit 400000) (nat_lit 0) (nat_lit 1) Bool.false (nat_lit 204299748) (nat_lit 400000) (nat_lit 0) (nat_lit 1) Gram665ProofSharing.c469)

noncomputable def Gram665ProofSharing.c510 := (@Enclosure.Complex.IsNear.im_isNear Gram665ProofSharing.c459 Bool.false (nat_lit 56167805762333799) (nat_lit 9007199254740992) (nat_lit 2500289) (nat_lit 34000000000000000) Bool.false (nat_lit 884004168074659) (nat_lit 562949953421312) (nat_lit 5000017) (nat_lit 34000000000000000) Gram665ProofSharing.c507)

noncomputable def Gram665ProofSharing.c511 := (@HPow.hPow.{0, 0, 0} Complex Int Complex Gram665ProofSharing.c242 Gram665ProofSharing.c112 Gram665ProofSharing.c333)

noncomputable def Gram665ProofSharing.c512 := (@HMul.hMul.{0, 0, 0} Complex Complex Complex (@instHMul.{0} Complex Complex.instMul) Gram665ProofSharing.c330 Gram665ProofSharing.c511)

noncomputable def Gram665ProofSharing.c513 := (nat_lit 51618212537973558249927066047343)

noncomputable def Gram665ProofSharing.c514 := (@HPow.hPow.{0, 0, 0} Complex Int Complex Gram665ProofSharing.c242 Gram665ProofSharing.c112 Gram665ProofSharing.c348)

noncomputable def Gram665ProofSharing.c515 := (@HMul.hMul.{0, 0, 0} Complex Complex Complex (@instHMul.{0} Complex Complex.instMul) Gram665ProofSharing.c345 Gram665ProofSharing.c514)

noncomputable def Gram665ProofSharing.c516 := (@Inv.inv.{0} Complex Complex.instInv Gram665ProofSharing.c115)

noncomputable def Gram665ProofSharing.c517 := (BSN.zpow_one_sub_two_mul Gram665ProofSharing.c112 (nat_lit 1) (nat_lit 1) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram665ProofSharing.c518 := (Enclosure.Complex.inv_re_eq_mul Gram665ProofSharing.c115)

noncomputable def Gram665ProofSharing.c519 := (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) (Gram665ProofSharing.c115 : ℂ).re (Gram665ProofSharing.c115 : ℂ).re)

noncomputable def Gram665ProofSharing.c520 := (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) (Gram665ProofSharing.c115 : ℂ).im (Gram665ProofSharing.c115 : ℂ).im)

noncomputable def Gram665ProofSharing.c521 := (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd) Gram665ProofSharing.c519 Gram665ProofSharing.c520)

noncomputable def Gram665ProofSharing.c522 := (Enclosure.Complex.normSq_eq_mul_add_mul Gram665ProofSharing.c115)

noncomputable def Gram665ProofSharing.c523 := (@Enclosure.Real.IsNear.mulLit_ff (Gram665ProofSharing.c115 : ℂ).re (Gram665ProofSharing.c115 : ℂ).re (nat_lit 100000) (nat_lit 400000) (nat_lit 0) (nat_lit 1) (nat_lit 100000) (nat_lit 400000) (nat_lit 0) (nat_lit 1) (nat_lit 1) (nat_lit 16) (nat_lit 0) (nat_lit 1) Gram665ProofSharing.c128 Gram665ProofSharing.c128 (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram665ProofSharing.c524 := (@Enclosure.Real.IsNear.mulLit_ff (Gram665ProofSharing.c115 : ℂ).im (Gram665ProofSharing.c115 : ℂ).im (nat_lit 204299748) (nat_lit 400000) (nat_lit 0) (nat_lit 1) (nat_lit 204299748) (nat_lit 400000) (nat_lit 0) (nat_lit 1) (nat_lit 2608649189553969) (nat_lit 10000000000) (nat_lit 0) (nat_lit 1) Gram665ProofSharing.c131 Gram665ProofSharing.c131 (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram665ProofSharing.c525 := (@Enclosure.Real.IsNear.addLit_ff Gram665ProofSharing.c519 Gram665ProofSharing.c520 (nat_lit 1) (nat_lit 16) (nat_lit 0) (nat_lit 1) (nat_lit 2608649189553969) (nat_lit 10000000000) (nat_lit 0) (nat_lit 1) (nat_lit 41738397032863504) (nat_lit 2608649814553969) (nat_lit 10000000000) (nat_lit 0) (nat_lit 1) Gram665ProofSharing.c523 Gram665ProofSharing.c524 (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram665ProofSharing.c526 := (@Neg.neg.{0} Real Real.instNeg (Gram665ProofSharing.c115 : ℂ).im)

noncomputable def Gram665ProofSharing.c527 := (Enclosure.Complex.inv_im_eq_mul Gram665ProofSharing.c115)

noncomputable def Gram665ProofSharing.c528 := (@Enclosure.Real.IsNear.neg (Gram665ProofSharing.c115 : ℂ).im Bool.false (nat_lit 204299748) (nat_lit 400000) (nat_lit 0) (nat_lit 1) Gram665ProofSharing.c131)

noncomputable def Gram665ProofSharing.c529 := (nat_lit 2475880078570760549798248448000000000)

noncomputable def Gram665ProofSharing.c530 := (nat_lit 12379400392853802748991242240000000000)

noncomputable def Gram665ProofSharing.c531 := (nat_lit 464563912841762024249343594426087)

noncomputable def Gram665ProofSharing.c532 := (nat_lit 61897001964269013744956211200000000000000)

noncomputable def Gram665ProofSharing.c533 := (nat_lit 309485009821345068724781056000000000000000)

noncomputable def Gram665ProofSharing.c534 := (@Inv.inv.{0} Complex Complex.instInv Gram665ProofSharing.c113)

noncomputable def Gram665ProofSharing.c535 := (BSN.zpow_one_sub_two_mul Gram665ProofSharing.c112 (nat_lit 2) (nat_lit 3) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram665ProofSharing.c536 := (Enclosure.Complex.inv_re_eq_mul Gram665ProofSharing.c113)

noncomputable def Gram665ProofSharing.c537 := (@Enclosure.Complex.IsNear.re_isNear Gram665ProofSharing.c113 Bool.true (nat_lit 7825946943661907) (nat_lit 40000000000) (nat_lit 0) (nat_lit 1) Bool.true (nat_lit 133236497246063149774953) (nat_lit 1000000000000000) (nat_lit 0) (nat_lit 1) Zeta.Certificates.Gram.gp11_cert._proof_6)

noncomputable def Gram665ProofSharing.c538 := (nat_lit 17752002476803671426113835695654750520171152209)

noncomputable def Gram665ProofSharing.c539 := (nat_lit 1000000000000000000000000000000)

noncomputable def Gram665ProofSharing.c540 := (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) (Gram665ProofSharing.c113 : ℂ).re (Gram665ProofSharing.c113 : ℂ).re)

noncomputable def Gram665ProofSharing.c541 := (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) (Gram665ProofSharing.c113 : ℂ).im (Gram665ProofSharing.c113 : ℂ).im)

noncomputable def Gram665ProofSharing.c542 := (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd) Gram665ProofSharing.c540 Gram665ProofSharing.c541)

noncomputable def Gram665ProofSharing.c543 := (Enclosure.Complex.normSq_eq_mul_add_mul Gram665ProofSharing.c113)

noncomputable def Gram665ProofSharing.c544 := (nat_lit 61245445565011143375838722876649)

noncomputable def Gram665ProofSharing.c545 := (nat_lit 17751964198400193294149225796452952614546152209)

noncomputable def Gram665ProofSharing.c546 := (nat_lit 28403203962885874281782137113047600832273843534400000000000000000000)

noncomputable def Gram665ProofSharing.c547 := (@Enclosure.Real.IsNear.mulLit_tt (Gram665ProofSharing.c113 : ℂ).re (Gram665ProofSharing.c113 : ℂ).re (nat_lit 7825946943661907) (nat_lit 40000000000) (nat_lit 0) (nat_lit 1) (nat_lit 7825946943661907) (nat_lit 40000000000) (nat_lit 0) (nat_lit 1) Gram665ProofSharing.c544 (nat_lit 1600000000000000000000) (nat_lit 0) (nat_lit 1) Gram665ProofSharing.c537 Gram665ProofSharing.c537 (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram665ProofSharing.c548 := (@Enclosure.Complex.IsNear.im_isNear Gram665ProofSharing.c113 Bool.true (nat_lit 7825946943661907) (nat_lit 40000000000) (nat_lit 0) (nat_lit 1) Bool.true (nat_lit 133236497246063149774953) (nat_lit 1000000000000000) (nat_lit 0) (nat_lit 1) Zeta.Certificates.Gram.gp11_cert._proof_6)

noncomputable def Gram665ProofSharing.c549 := (@Enclosure.Real.IsNear.mulLit_tt (Gram665ProofSharing.c113 : ℂ).im (Gram665ProofSharing.c113 : ℂ).im (nat_lit 133236497246063149774953) (nat_lit 1000000000000000) (nat_lit 0) (nat_lit 1) (nat_lit 133236497246063149774953) (nat_lit 1000000000000000) (nat_lit 0) (nat_lit 1) Gram665ProofSharing.c545 Gram665ProofSharing.c539 (nat_lit 0) (nat_lit 1) Gram665ProofSharing.c548 Gram665ProofSharing.c548 (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram665ProofSharing.c550 := (@Enclosure.Real.IsNear.addLit_ff Gram665ProofSharing.c540 Gram665ProofSharing.c541 Gram665ProofSharing.c544 (nat_lit 1600000000000000000000) (nat_lit 0) (nat_lit 1) Gram665ProofSharing.c545 Gram665ProofSharing.c539 (nat_lit 0) (nat_lit 1) Gram665ProofSharing.c546 Gram665ProofSharing.c538 Gram665ProofSharing.c539 (nat_lit 0) (nat_lit 1) Gram665ProofSharing.c547 Gram665ProofSharing.c549 (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram665ProofSharing.c551 := (@Neg.neg.{0} Real Real.instNeg (Gram665ProofSharing.c113 : ℂ).im)

noncomputable def Gram665ProofSharing.c552 := (Enclosure.Complex.inv_im_eq_mul Gram665ProofSharing.c113)

noncomputable def Gram665ProofSharing.c553 := (@Enclosure.Real.IsNear.neg (Gram665ProofSharing.c113 : ℂ).im Bool.true (nat_lit 133236497246063149774953) (nat_lit 1000000000000000) (nat_lit 0) (nat_lit 1) Gram665ProofSharing.c548)

noncomputable def Gram665ProofSharing.c554 := (BSN.logSumC Gram665ProofSharing.c107 (nat_lit 0))

noncomputable def Gram665ProofSharing.c555 := (Enclosure.sfrac Bool.false (nat_lit 98304000000000000000000000) Gram665ProofSharing.c144)


