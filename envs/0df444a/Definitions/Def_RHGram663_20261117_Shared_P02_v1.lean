-- Prove2me | Definitions.Def_RHGram663_20261117_Shared_P02_v1
-- name    : RHGram663_20261117_Shared_P02_v1
-- status  : Definition
-- author  : @bueno_ricardo
-- created : 2026-11-17T23:12:42.320983+00:00
-- url     : https://prove2.me/theorems/df3ddbc4-c73f-4718-ad59-5358e7d7d623
-- title:
--   Gram 663 ordinary shared terms, part 2
-- statement:
--   Exact shared expressions and complete ordinary auxiliary proofs for the endpoint certificate of Gram point 663. No additional axioms or custom proof generators. Imports the already published analytic and numerical support modules.
-- source:
--   Salvatore Mercuri and Bhavik Mehta, smmercuri/zeta commit 3dab6480a82f1bfc5de0a59550e279cf50490033; Apache-2.0. Ordinary proof export and exact sharing by Desenvolvimento RH. Full expanded strict AXLE and cumulative prefixes: dd19be12-cc1a-4ab1-a22a-5a75d0071122.

import Definitions.Def_RHGram663_20261117_Shared_P01_v1
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
noncomputable def Gram663ProofSharing.c225 := (@HDiv.hDiv.{0, 0, 0} Real Real Real Gram663ProofSharing.c15 Gram663ProofSharing.c39 Gram663ProofSharing.c6)

noncomputable def Gram663ProofSharing.c226 := (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) Gram663ProofSharing.c225 (Real.log Real.pi))

noncomputable def Gram663ProofSharing.c227 := (nat_lit 19010952715307424945173079977445984458365921597)

noncomputable def Gram663ProofSharing.c228 := (nat_lit 47357911681696057420042597242211207472903)

noncomputable def Gram663ProofSharing.c229 := (nat_lit 571144128683830375610715507769018793459003)

noncomputable def Gram663ProofSharing.c230 := (nat_lit 713053462628379038341895553024000000000)

noncomputable def Gram663ProofSharing.c231 := (nat_lit 5923658698955253537851764586441902701649)

noncomputable def Gram663ProofSharing.c232 := (nat_lit 76597539930782904509383311360000000000000000000)

noncomputable def Gram663ProofSharing.c233 := (@HDiv.hDiv.{0, 0, 0} Complex Complex Complex Gram663ProofSharing.c28 Gram663ProofSharing.c30 Gram663ProofSharing.c42)

noncomputable def Gram663ProofSharing.c234 := (@HSub.hSub.{0, 0, 0} Complex Complex Complex (@instHSub.{0} Complex Complex.instSub) Gram663ProofSharing.c47 Gram663ProofSharing.c233)

noncomputable def Gram663ProofSharing.c235 := (Complex.log Gram663ProofSharing.c47)

noncomputable def Gram663ProofSharing.c236 := (@HMul.hMul.{0, 0, 0} Complex Complex Complex (@instHMul.{0} Complex Complex.instMul) Gram663ProofSharing.c234 Gram663ProofSharing.c235)

noncomputable def Gram663ProofSharing.c237 := (@HSub.hSub.{0, 0, 0} Complex Complex Complex (@instHSub.{0} Complex Complex.instSub) Gram663ProofSharing.c236 Gram663ProofSharing.c47)

noncomputable def Gram663ProofSharing.c238 := (@HMul.hMul.{0, 0, 0} Complex Complex Complex (@instHMul.{0} Complex Complex.instMul) Gram663ProofSharing.c233 ↑Gram663ProofSharing.c8)

noncomputable def Gram663ProofSharing.c239 := (@HAdd.hAdd.{0, 0, 0} Complex Complex Complex (@instHAdd.{0} Complex Complex.instAdd) Gram663ProofSharing.c237 Gram663ProofSharing.c238)

noncomputable def Gram663ProofSharing.c240 := (@DivInvMonoid.toZPow.{0} Complex Complex.instDivInvMonoid)

noncomputable def Gram663ProofSharing.c241 := (@ZPow.toPow.{0} Complex Gram663ProofSharing.c240)

noncomputable def Gram663ProofSharing.c242 := (@instHPow.{0, 0} Complex Int Gram663ProofSharing.c241)

noncomputable def Gram663ProofSharing.c243 := (@OfNat.ofNat.{0} Int (nat_lit 1) (@instOfNat (nat_lit 1)))

noncomputable def Gram663ProofSharing.c244 := (@OfNat.ofNat.{0} Int (nat_lit 2) (@instOfNat (nat_lit 2)))

noncomputable def Gram663ProofSharing.c245 := (nat_lit 57222535635135671380879753740997)

noncomputable def Gram663ProofSharing.c246 := (nat_lit 1166229138610374995352109807413634078403)

noncomputable def Gram663ProofSharing.c247 := (BSN.w_sub_half_zero_mk Gram663ProofSharing.c39 Bool.false (nat_lit 101902985) (nat_lit 100000) Gram663ProofSharing.c56 (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram663ProofSharing.c248 := (Enclosure.sfrac Bool.true (nat_lit 100000) (nat_lit 400000))

noncomputable def Gram663ProofSharing.c249 := (Enclosure.Real.IsNear.const Bool.true (nat_lit 100000) (nat_lit 400000))

noncomputable def Gram663ProofSharing.c250 := (@Enclosure.Complex.IsNear.mk Gram663ProofSharing.c248 Gram663ProofSharing.c59 Bool.true (nat_lit 100000) (nat_lit 400000) (nat_lit 0) (nat_lit 1) Bool.false (nat_lit 203805970) (nat_lit 400000) (nat_lit 0) (nat_lit 1) Gram663ProofSharing.c249 Gram663ProofSharing.c61)

noncomputable def Gram663ProofSharing.c251 := (@Enclosure.Complex.IsNear.of_eq Gram663ProofSharing.c234 { re := Enclosure.sfrac Bool.true (nat_lit 100000) (nat_lit 400000), im := Enclosure.sfrac Bool.false (nat_lit 203805970) (nat_lit 400000) } Bool.true (nat_lit 100000) (nat_lit 400000) (nat_lit 0) (nat_lit 1) Bool.false (nat_lit 203805970) (nat_lit 400000) (nat_lit 0) (nat_lit 1) Gram663ProofSharing.c247 Gram663ProofSharing.c250)

noncomputable def Gram663ProofSharing.c252 := (@Enclosure.Complex.IsNear.re_isNear Gram663ProofSharing.c234 Bool.true (nat_lit 100000) (nat_lit 400000) (nat_lit 0) (nat_lit 1) Bool.false (nat_lit 203805970) (nat_lit 400000) (nat_lit 0) (nat_lit 1) Gram663ProofSharing.c251)

noncomputable def Gram663ProofSharing.c253 := (Complex.log { re := Enclosure.sfrac Bool.false (nat_lit 100000) (nat_lit 400000), im := Enclosure.sfrac Bool.false (nat_lit 203805970) (nat_lit 400000) })

noncomputable def Gram663ProofSharing.c254 := (@congrArg.{1, 1} Complex Complex Gram663ProofSharing.c47 { re := Enclosure.sfrac Bool.false (nat_lit 100000) (nat_lit 400000), im := Enclosure.sfrac Bool.false (nat_lit 203805970) (nat_lit 400000) } Complex.log Gram663ProofSharing.c57)

noncomputable def Gram663ProofSharing.c255 := (Enclosure.sfrac Bool.false (nat_lit 1) (nat_lit 2))

noncomputable def Gram663ProofSharing.c256 := (Enclosure.sfrac Bool.false (nat_lit 41536883407640900) (nat_lit 160000000000))

noncomputable def Gram663ProofSharing.c257 := (Real.log Gram663ProofSharing.c256)

noncomputable def Gram663ProofSharing.c258 := (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) Gram663ProofSharing.c255 Gram663ProofSharing.c257)

noncomputable def Gram663ProofSharing.c259 := (Enclosure.clog_re_eq (nat_lit 100000) (nat_lit 203805970) (nat_lit 400000) (nat_lit 41536883407640900) (nat_lit 160000000000) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram663ProofSharing.c260 := (Enclosure.Real.IsNear.const Bool.false (nat_lit 1) (nat_lit 2))

noncomputable def Gram663ProofSharing.c261 := (@Nat.cast.{0} Real Real.instNatCast (nat_lit 41536883407640900))

noncomputable def Gram663ProofSharing.c262 := (@Nat.cast.{0} Real Real.instNatCast (nat_lit 160000000000))

noncomputable def Gram663ProofSharing.c263 := (@HDiv.hDiv.{0, 0, 0} Real Real Real Gram663ProofSharing.c15 Gram663ProofSharing.c261 Gram663ProofSharing.c262)

noncomputable def Gram663ProofSharing.c264 := (Real.log Gram663ProofSharing.c263)

noncomputable def Gram663ProofSharing.c265 := (nat_lit 11403785704291211447771394409496550972645508913019009473335613777386940865261090441767119009413947767132800090874527612821237445545285298357773550807544581891085886980554903183985681421807599992725415522376347159193433883366179503385022904535213442253058725148874533474681534124585515399085927860900067705750000000000000000000000000000000000000000)

noncomputable def Gram663ProofSharing.c266 := (nat_lit 440435400605997971757852508043249149087058195174392000500699237592846466802205881528720355845834083318103313540289747427174150027267709320738902490623906720245206711860425974866728605367108940722415593347704095166478005229116034866937954529137333807957662783297175299730443813226025810664405120423076673200000000000000000000000000000000000000000)

noncomputable def Gram663ProofSharing.c267 := (nat_lit 119891775765031828091367237277460094928733062373079633206494885573925171455685863017582276973929985999867216815102863457334903572870993174291985504637908408307967233344662288856749556259993512840484524616020472754995330281591122548161820077675749688513630903157658188792499709184116805566669890750000000000000000000000000000000000000000)

noncomputable def Gram663ProofSharing.c268 := (BSN.artanhP (nat_lit 20565363407640900))

noncomputable def Gram663ProofSharing.c269 := (BSN.artanhQ (nat_lit 62508403407640900))

noncomputable def Gram663ProofSharing.c270 := (@BSN.binarySplit_of_base10 Gram663ProofSharing.c268 Gram663ProofSharing.c269 (nat_lit 0) (nat_lit 10) Gram663ProofSharing.c266 Gram663ProofSharing.c265 Gram663ProofSharing.c267 (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram663ProofSharing.c271 := (BSN.log_dyadic_bound (nat_lit 20565363407640900) (nat_lit 62508403407640900) (nat_lit 11) (nat_lit 10) Gram663ProofSharing.c265 (nat_lit 17179869184) (nat_lit 6600000000) Gram663ProofSharing.c266 Gram663ProofSharing.c267 (nat_lit 11741005424) (nat_lit 83073766815281800) (nat_lit 41943040000000000) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) Gram663ProofSharing.c270 (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram663ProofSharing.c272 := (BSN.log_rat_reduce_isNear (nat_lit 41536883407640900) (nat_lit 160000000000) (nat_lit 17) (nat_lit 83073766815281800) (nat_lit 41943040000000000) (nat_lit 11741005424) (nat_lit 17179869184) (nat_lit 24973259072661432) (nat_lit 36028797018963968) (nat_lit 6600000000) (nat_lit 1000000000000000) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) Gram663ProofSharing.c271 BSN.log2_near_15 (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram663ProofSharing.c273 := (@Enclosure.Real.IsNear.recentre' Gram663ProofSharing.c264 Bool.false (nat_lit 7716648808649748371344457728) (nat_lit 618970019642690137449562112) (nat_lit 1000112200000000) (nat_lit 6600000000000000000000000) (nat_lit 56146009655274599) (nat_lit 4503599627370496) (nat_lit 5000561) (nat_lit 33000000000000000) Gram663ProofSharing.c272 (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram663ProofSharing.c274 := (BSN.isNear_log_sfrac (nat_lit 41536883407640900) (nat_lit 160000000000) (nat_lit 56146009655274599) (nat_lit 4503599627370496) (nat_lit 5000561) (nat_lit 33000000000000000) Bool.false Gram663ProofSharing.c273)

noncomputable def Gram663ProofSharing.c275 := (@Enclosure.Real.IsNear.mulLit_ff Gram663ProofSharing.c255 Gram663ProofSharing.c257 (nat_lit 1) (nat_lit 2) (nat_lit 0) (nat_lit 1) (nat_lit 56146009655274599) (nat_lit 4503599627370496) (nat_lit 5000561) (nat_lit 33000000000000000) (nat_lit 56146009655274599) (nat_lit 9007199254740992) (nat_lit 5000561) (nat_lit 66000000000000000) Gram663ProofSharing.c260 Gram663ProofSharing.c274 (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram663ProofSharing.c276 := (@Enclosure.Real.IsNear.of_eq (Gram663ProofSharing.c253 : ℂ).re Gram663ProofSharing.c258 Bool.false (nat_lit 56146009655274599) (nat_lit 9007199254740992) (nat_lit 5000561) (nat_lit 66000000000000000) Gram663ProofSharing.c259 Gram663ProofSharing.c275)

noncomputable def Gram663ProofSharing.c277 := (@Nat.cast.{0} Real Real.instNatCast (nat_lit 203805970))

noncomputable def Gram663ProofSharing.c278 := (@Nat.cast.{0} Real Real.instNatCast (nat_lit 100000))

noncomputable def Gram663ProofSharing.c279 := (@HDiv.hDiv.{0, 0, 0} Real Real Real Gram663ProofSharing.c15 Gram663ProofSharing.c277 Gram663ProofSharing.c278)

noncomputable def Gram663ProofSharing.c280 := (Real.arctan Gram663ProofSharing.c279)

noncomputable def Gram663ProofSharing.c281 := (Enclosure.clog_im_eq (nat_lit 100000) (nat_lit 203805970) (nat_lit 400000) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram663ProofSharing.c282 := (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) Gram663ProofSharing.c255 Real.pi)

noncomputable def Gram663ProofSharing.c283 := (@HDiv.hDiv.{0, 0, 0} Real Real Real Gram663ProofSharing.c15 Gram663ProofSharing.c278 Gram663ProofSharing.c277)

noncomputable def Gram663ProofSharing.c284 := (Real.arctan Gram663ProofSharing.c283)

noncomputable def Gram663ProofSharing.c285 := (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) Gram663ProofSharing.c282 Gram663ProofSharing.c284)

noncomputable def Gram663ProofSharing.c286 := (BSN.arctan_recip (nat_lit 203805970) (nat_lit 100000) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram663ProofSharing.c287 := (@Enclosure.Real.IsNear.mulLit_ff Gram663ProofSharing.c255 Real.pi (nat_lit 1) (nat_lit 2) (nat_lit 0) (nat_lit 1) (nat_lit 226375608064910080) (nat_lit 72057594037927936) (nat_lit 1) (nat_lit 1000000000000000) (nat_lit 884279719003555) (nat_lit 562949953421312) (nat_lit 1) (nat_lit 2000000000000000) Gram663ProofSharing.c260 BSN.pi_near_15 (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram663ProofSharing.c288 := (@BSN.binarySplit_of_le (BSN.arctanEvenP (nat_lit 100000)) (BSN.arctanEvenQ (nat_lit 203805970)) (nat_lit 0) (nat_lit 0) (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram663ProofSharing.c289 := (@BSN.binarySplit_of_le (BSN.arctanOddP (nat_lit 100000)) (BSN.arctanOddQ (nat_lit 203805970)) (nat_lit 0) (nat_lit 0) (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram663ProofSharing.c290 := (BSN.arctan_dyadic_bound_f (nat_lit 100000) (nat_lit 203805970) (nat_lit 1) (nat_lit 0) (nat_lit 17179869184) (nat_lit 6600000000) (nat_lit 0) (nat_lit 1) (nat_lit 1) (nat_lit 0) (nat_lit 1) (nat_lit 1) (nat_lit 8429521) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) Gram663ProofSharing.c288 Gram663ProofSharing.c289 (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram663ProofSharing.c291 := (@Enclosure.Real.IsNear.subLit_ff_p Gram663ProofSharing.c282 Gram663ProofSharing.c284 (nat_lit 884279719003555) (nat_lit 562949953421312) (nat_lit 1) (nat_lit 2000000000000000) (nat_lit 8429521) (nat_lit 17179869184) (nat_lit 1) (nat_lit 6600000000) (nat_lit 15187064496091039759597568) (nat_lit 884003500459427) (nat_lit 562949953421312) (nat_lit 10000033) (nat_lit 66000000000000000) Gram663ProofSharing.c287 Gram663ProofSharing.c290 (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram663ProofSharing.c292 := (@Enclosure.Real.IsNear.of_eq Gram663ProofSharing.c280 Gram663ProofSharing.c285 Bool.false (nat_lit 884003500459427) (nat_lit 562949953421312) (nat_lit 10000033) (nat_lit 66000000000000000) Gram663ProofSharing.c286 Gram663ProofSharing.c291)

noncomputable def Gram663ProofSharing.c293 := (@Enclosure.Real.IsNear.of_eq (Gram663ProofSharing.c253 : ℂ).im Gram663ProofSharing.c280 Bool.false (nat_lit 884003500459427) (nat_lit 562949953421312) (nat_lit 10000033) (nat_lit 66000000000000000) Gram663ProofSharing.c281 Gram663ProofSharing.c292)

noncomputable def Gram663ProofSharing.c294 := (@Enclosure.Complex.IsNear.of_parts Gram663ProofSharing.c253 Bool.false (nat_lit 56146009655274599) (nat_lit 9007199254740992) (nat_lit 5000561) (nat_lit 66000000000000000) Bool.false (nat_lit 884003500459427) (nat_lit 562949953421312) (nat_lit 10000033) (nat_lit 66000000000000000) Gram663ProofSharing.c276 Gram663ProofSharing.c293)

noncomputable def Gram663ProofSharing.c295 := (@Enclosure.Complex.IsNear.of_eq Gram663ProofSharing.c235 Gram663ProofSharing.c253 Bool.false (nat_lit 56146009655274599) (nat_lit 9007199254740992) (nat_lit 5000561) (nat_lit 66000000000000000) Bool.false (nat_lit 884003500459427) (nat_lit 562949953421312) (nat_lit 10000033) (nat_lit 66000000000000000) Gram663ProofSharing.c254 Gram663ProofSharing.c294)

noncomputable def Gram663ProofSharing.c296 := (@Enclosure.Complex.IsNear.re_isNear Gram663ProofSharing.c235 Bool.false (nat_lit 56146009655274599) (nat_lit 9007199254740992) (nat_lit 5000561) (nat_lit 66000000000000000) Bool.false (nat_lit 884003500459427) (nat_lit 562949953421312) (nat_lit 10000033) (nat_lit 66000000000000000) Gram663ProofSharing.c295)

noncomputable def Gram663ProofSharing.c297 := (@Enclosure.Complex.IsNear.im_isNear Gram663ProofSharing.c234 Bool.true (nat_lit 100000) (nat_lit 400000) (nat_lit 0) (nat_lit 1) Bool.false (nat_lit 203805970) (nat_lit 400000) (nat_lit 0) (nat_lit 1) Gram663ProofSharing.c251)

noncomputable def Gram663ProofSharing.c298 := (@Enclosure.Complex.IsNear.im_isNear Gram663ProofSharing.c235 Bool.false (nat_lit 56146009655274599) (nat_lit 9007199254740992) (nat_lit 5000561) (nat_lit 66000000000000000) Bool.false (nat_lit 884003500459427) (nat_lit 562949953421312) (nat_lit 10000033) (nat_lit 66000000000000000) Gram663ProofSharing.c295)

noncomputable def Gram663ProofSharing.c299 := (↑Gram663ProofSharing.c8)

noncomputable def Gram663ProofSharing.c300 := (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) (Gram663ProofSharing.c233 : ℂ).re (Gram663ProofSharing.c299 : ℂ).re)

noncomputable def Gram663ProofSharing.c301 := (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) (Gram663ProofSharing.c233 : ℂ).im (Gram663ProofSharing.c299 : ℂ).im)

noncomputable def Gram663ProofSharing.c302 := (Enclosure.sfrac Bool.false (nat_lit 0) (nat_lit 1))

noncomputable def Gram663ProofSharing.c303 := (Enclosure.Real.IsNear.const Bool.false (nat_lit 0) (nat_lit 1))

noncomputable def Gram663ProofSharing.c304 := (@Enclosure.Complex.IsNear.mk Gram663ProofSharing.c255 Gram663ProofSharing.c302 Bool.false (nat_lit 1) (nat_lit 2) (nat_lit 0) (nat_lit 1) Bool.false (nat_lit 0) (nat_lit 1) (nat_lit 0) (nat_lit 1) Gram663ProofSharing.c260 Gram663ProofSharing.c303)

noncomputable def Gram663ProofSharing.c305 := (@Enclosure.Complex.IsNear.of_eq Gram663ProofSharing.c233 { re := Enclosure.sfrac Bool.false (nat_lit 1) (nat_lit 2), im := Enclosure.sfrac Bool.false (nat_lit 0) (nat_lit 1) } Bool.false (nat_lit 1) (nat_lit 2) (nat_lit 0) (nat_lit 1) Bool.false (nat_lit 0) (nat_lit 1) (nat_lit 0) (nat_lit 1) BSN.half_c_mk Gram663ProofSharing.c304)

noncomputable def Gram663ProofSharing.c306 := (@Enclosure.Complex.IsNear.re_isNear Gram663ProofSharing.c233 Bool.false (nat_lit 1) (nat_lit 2) (nat_lit 0) (nat_lit 1) Bool.false (nat_lit 0) (nat_lit 1) (nat_lit 0) (nat_lit 1) Gram663ProofSharing.c305)

noncomputable def Gram663ProofSharing.c307 := (Complex.ofReal_re Gram663ProofSharing.c8)

noncomputable def Gram663ProofSharing.c308 := (@Enclosure.Real.IsNear.of_eq (Gram663ProofSharing.c299 : ℂ).re Gram663ProofSharing.c8 Bool.false (nat_lit 3946810947) (nat_lit 2147483648) (nat_lit 1) (nat_lit 4294967296) Gram663ProofSharing.c307 Zeta.Certificates.Gram.gp9_cert._proof_1)

noncomputable def Gram663ProofSharing.c309 := (@Enclosure.Real.IsNear.mulLit_ff (Gram663ProofSharing.c233 : ℂ).re (Gram663ProofSharing.c299 : ℂ).re (nat_lit 1) (nat_lit 2) (nat_lit 0) (nat_lit 1) (nat_lit 3946810947) (nat_lit 2147483648) (nat_lit 1) (nat_lit 4294967296) (nat_lit 3946810947) (nat_lit 4294967296) (nat_lit 1) (nat_lit 8589934592) Gram663ProofSharing.c306 Gram663ProofSharing.c308 (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram663ProofSharing.c310 := (@Enclosure.Complex.IsNear.im_isNear Gram663ProofSharing.c233 Bool.false (nat_lit 1) (nat_lit 2) (nat_lit 0) (nat_lit 1) Bool.false (nat_lit 0) (nat_lit 1) (nat_lit 0) (nat_lit 1) Gram663ProofSharing.c305)

noncomputable def Gram663ProofSharing.c311 := (Complex.ofReal_im Gram663ProofSharing.c8)

noncomputable def Gram663ProofSharing.c312 := (@Eq.trans.{1} Real (Gram663ProofSharing.c299 : ℂ).im Gram663ProofSharing.c147 Gram663ProofSharing.c302 Gram663ProofSharing.c311 Enclosure.sfrac_zero_eq)

noncomputable def Gram663ProofSharing.c313 := (@Enclosure.Real.IsNear.of_eq (Gram663ProofSharing.c299 : ℂ).im Gram663ProofSharing.c302 Bool.false (nat_lit 0) (nat_lit 1) (nat_lit 0) (nat_lit 1) Gram663ProofSharing.c312 Gram663ProofSharing.c303)

noncomputable def Gram663ProofSharing.c314 := (@Enclosure.Real.IsNear.mulLit_ff (Gram663ProofSharing.c233 : ℂ).im (Gram663ProofSharing.c299 : ℂ).im (nat_lit 0) (nat_lit 1) (nat_lit 0) (nat_lit 1) (nat_lit 0) (nat_lit 1) (nat_lit 0) (nat_lit 1) (nat_lit 0) (nat_lit 1) (nat_lit 0) (nat_lit 1) Gram663ProofSharing.c310 Gram663ProofSharing.c313 (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram663ProofSharing.c315 := (@Enclosure.Real.IsNear.subLit_ff_p Gram663ProofSharing.c300 Gram663ProofSharing.c301 (nat_lit 3946810947) (nat_lit 4294967296) (nat_lit 1) (nat_lit 8589934592) (nat_lit 0) (nat_lit 1) (nat_lit 0) (nat_lit 1) (nat_lit 3946810947) (nat_lit 3946810947) (nat_lit 4294967296) (nat_lit 1) (nat_lit 8589934592) Gram663ProofSharing.c309 Gram663ProofSharing.c314 (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram663ProofSharing.c316 := (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) (Gram663ProofSharing.c233 : ℂ).re (Gram663ProofSharing.c299 : ℂ).im)

noncomputable def Gram663ProofSharing.c317 := (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) (Gram663ProofSharing.c233 : ℂ).im (Gram663ProofSharing.c299 : ℂ).re)

noncomputable def Gram663ProofSharing.c318 := (@Enclosure.Real.IsNear.mulLit_ff (Gram663ProofSharing.c233 : ℂ).re (Gram663ProofSharing.c299 : ℂ).im (nat_lit 1) (nat_lit 2) (nat_lit 0) (nat_lit 1) (nat_lit 0) (nat_lit 1) (nat_lit 0) (nat_lit 1) (nat_lit 0) (nat_lit 1) (nat_lit 0) (nat_lit 1) Gram663ProofSharing.c306 Gram663ProofSharing.c313 (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram663ProofSharing.c319 := (@Enclosure.Real.IsNear.mulLit_ff (Gram663ProofSharing.c233 : ℂ).im (Gram663ProofSharing.c299 : ℂ).re (nat_lit 0) (nat_lit 1) (nat_lit 0) (nat_lit 1) (nat_lit 3946810947) (nat_lit 2147483648) (nat_lit 1) (nat_lit 4294967296) (nat_lit 0) (nat_lit 1) (nat_lit 0) (nat_lit 1) Gram663ProofSharing.c310 Gram663ProofSharing.c308 (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram663ProofSharing.c320 := (@Enclosure.Real.IsNear.addLit_ff Gram663ProofSharing.c316 Gram663ProofSharing.c317 (nat_lit 0) (nat_lit 1) (nat_lit 0) (nat_lit 1) (nat_lit 0) (nat_lit 1) (nat_lit 0) (nat_lit 1) (nat_lit 0) (nat_lit 0) (nat_lit 1) (nat_lit 0) (nat_lit 1) Gram663ProofSharing.c318 Gram663ProofSharing.c319 (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram663ProofSharing.c321 := (@Enclosure.Complex.IsNear.mul Gram663ProofSharing.c233 Gram663ProofSharing.c299 Bool.false (nat_lit 3946810947) (nat_lit 4294967296) (nat_lit 1) (nat_lit 8589934592) Bool.false (nat_lit 0) (nat_lit 1) (nat_lit 0) (nat_lit 1) Gram663ProofSharing.c315 Gram663ProofSharing.c320)

noncomputable def Gram663ProofSharing.c322 := (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) Gram663ProofSharing.c32 (nat_lit 2))

noncomputable def Gram663ProofSharing.c323 := (bernoulli Gram663ProofSharing.c322)

noncomputable def Gram663ProofSharing.c324 := (@Rat.cast.{0} Complex Complex.instRatCast Gram663ProofSharing.c323)

noncomputable def Gram663ProofSharing.c325 := (@Nat.cast.{0} Complex Complex.instNatCast (nat_lit 2))

noncomputable def Gram663ProofSharing.c326 := (@HMul.hMul.{0, 0, 0} Complex Complex Complex (@instHMul.{0} Complex Complex.instMul) Gram663ProofSharing.c42 Gram663ProofSharing.c325)

noncomputable def Gram663ProofSharing.c327 := (@HSub.hSub.{0, 0, 0} Complex Complex Complex (@instHSub.{0} Complex Complex.instSub) Gram663ProofSharing.c326 Gram663ProofSharing.c30)

noncomputable def Gram663ProofSharing.c328 := (@HMul.hMul.{0, 0, 0} Complex Complex Complex (@instHMul.{0} Complex Complex.instMul) Gram663ProofSharing.c326 Gram663ProofSharing.c327)

noncomputable def Gram663ProofSharing.c329 := (@HDiv.hDiv.{0, 0, 0} Complex Complex Complex Gram663ProofSharing.c28 Gram663ProofSharing.c324 Gram663ProofSharing.c328)

noncomputable def Gram663ProofSharing.c330 := (@Nat.cast.{0} Int instNatCastInt (nat_lit 2))

noncomputable def Gram663ProofSharing.c331 := (@HMul.hMul.{0, 0, 0} Int Int Int (@instHMul.{0} Int Int.instMul) Gram663ProofSharing.c244 Gram663ProofSharing.c330)

noncomputable def Gram663ProofSharing.c332 := (@HSub.hSub.{0, 0, 0} Int Int Int (@instHSub.{0} Int Int.instSub) Gram663ProofSharing.c243 Gram663ProofSharing.c331)

noncomputable def Gram663ProofSharing.c333 := (@HPow.hPow.{0, 0, 0} Complex Int Complex Gram663ProofSharing.c242 Gram663ProofSharing.c47 Gram663ProofSharing.c332)

noncomputable def Gram663ProofSharing.c334 := (@HMul.hMul.{0, 0, 0} Complex Complex Complex (@instHMul.{0} Complex Complex.instMul) Gram663ProofSharing.c329 Gram663ProofSharing.c333)

noncomputable def Gram663ProofSharing.c335 := (nat_lit 149743587878546514999093634078403)

noncomputable def Gram663ProofSharing.c336 := (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) Gram663ProofSharing.c32 (nat_lit 1))

noncomputable def Gram663ProofSharing.c337 := (bernoulli Gram663ProofSharing.c336)

noncomputable def Gram663ProofSharing.c338 := (@Rat.cast.{0} Complex Complex.instRatCast Gram663ProofSharing.c337)

noncomputable def Gram663ProofSharing.c339 := (@Nat.cast.{0} Complex Complex.instNatCast (nat_lit 1))

noncomputable def Gram663ProofSharing.c340 := (@HMul.hMul.{0, 0, 0} Complex Complex Complex (@instHMul.{0} Complex Complex.instMul) Gram663ProofSharing.c42 Gram663ProofSharing.c339)

noncomputable def Gram663ProofSharing.c341 := (@HSub.hSub.{0, 0, 0} Complex Complex Complex (@instHSub.{0} Complex Complex.instSub) Gram663ProofSharing.c340 Gram663ProofSharing.c30)

noncomputable def Gram663ProofSharing.c342 := (@HMul.hMul.{0, 0, 0} Complex Complex Complex (@instHMul.{0} Complex Complex.instMul) Gram663ProofSharing.c340 Gram663ProofSharing.c341)

noncomputable def Gram663ProofSharing.c343 := (@HDiv.hDiv.{0, 0, 0} Complex Complex Complex Gram663ProofSharing.c28 Gram663ProofSharing.c338 Gram663ProofSharing.c342)

noncomputable def Gram663ProofSharing.c344 := (@Nat.cast.{0} Int instNatCastInt (nat_lit 1))

noncomputable def Gram663ProofSharing.c345 := (@HMul.hMul.{0, 0, 0} Int Int Int (@instHMul.{0} Int Int.instMul) Gram663ProofSharing.c244 Gram663ProofSharing.c344)

noncomputable def Gram663ProofSharing.c346 := (@HSub.hSub.{0, 0, 0} Int Int Int (@instHSub.{0} Int Int.instSub) Gram663ProofSharing.c243 Gram663ProofSharing.c345)

noncomputable def Gram663ProofSharing.c347 := (@HPow.hPow.{0, 0, 0} Complex Int Complex Gram663ProofSharing.c242 Gram663ProofSharing.c47 Gram663ProofSharing.c346)

noncomputable def Gram663ProofSharing.c348 := (@HMul.hMul.{0, 0, 0} Complex Complex Complex (@instHMul.{0} Complex Complex.instMul) Gram663ProofSharing.c343 Gram663ProofSharing.c347)

noncomputable def Gram663ProofSharing.c349 := (@Enclosure.Complex.IsNear.mk Gram663ProofSharing.c302 Gram663ProofSharing.c302 Bool.false (nat_lit 0) (nat_lit 1) (nat_lit 0) (nat_lit 1) Bool.false (nat_lit 0) (nat_lit 1) (nat_lit 0) (nat_lit 1) Gram663ProofSharing.c303 Gram663ProofSharing.c303)

noncomputable def Gram663ProofSharing.c350 := (BSN.stirling_coeff_mk (nat_lit 1) (nat_lit 1) (nat_lit 6) Bool.false BSN.bern_real_1 (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram663ProofSharing.c351 := (Enclosure.sfrac Bool.false (nat_lit 1) (nat_lit 12))

noncomputable def Gram663ProofSharing.c352 := (Enclosure.Real.IsNear.const Bool.false (nat_lit 1) (nat_lit 12))

noncomputable def Gram663ProofSharing.c353 := (@Enclosure.Complex.IsNear.mk Gram663ProofSharing.c351 Gram663ProofSharing.c302 Bool.false (nat_lit 1) (nat_lit 12) (nat_lit 0) (nat_lit 1) Bool.false (nat_lit 0) (nat_lit 1) (nat_lit 0) (nat_lit 1) Gram663ProofSharing.c352 Gram663ProofSharing.c303)

noncomputable def Gram663ProofSharing.c354 := (@Enclosure.Complex.IsNear.of_eq Gram663ProofSharing.c343 { re := Enclosure.sfrac Bool.false (nat_lit 1) (nat_lit 12), im := Enclosure.sfrac Bool.false (nat_lit 0) (nat_lit 1) } Bool.false (nat_lit 1) (nat_lit 12) (nat_lit 0) (nat_lit 1) Bool.false (nat_lit 0) (nat_lit 1) (nat_lit 0) (nat_lit 1) Gram663ProofSharing.c350 Gram663ProofSharing.c353)

noncomputable def Gram663ProofSharing.c355 := (@Enclosure.Complex.IsNear.re_isNear Gram663ProofSharing.c343 Bool.false (nat_lit 1) (nat_lit 12) (nat_lit 0) (nat_lit 1) Bool.false (nat_lit 0) (nat_lit 1) (nat_lit 0) (nat_lit 1) Gram663ProofSharing.c354)

noncomputable def Gram663ProofSharing.c356 := (@Inv.inv.{0} Complex Complex.instInv Gram663ProofSharing.c50)

noncomputable def Gram663ProofSharing.c357 := (BSN.zpow_one_sub_two_mul Gram663ProofSharing.c47 (nat_lit 1) (nat_lit 1) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram663ProofSharing.c358 := (@instMulZeroOneClassOfSemiring.{0} Complex Complex.instSemiring)

noncomputable def Gram663ProofSharing.c359 := (@instMulZeroOneClassOfSemiring.{0} Real Real.semiring)

noncomputable def Gram663ProofSharing.c360 := (@MonoidWithZeroHom.{0, 0} Complex Real Gram663ProofSharing.c358 Gram663ProofSharing.c359)

noncomputable def Gram663ProofSharing.c361 := (@MonoidWithZeroHom.funLike.{0, 0} Complex Real Gram663ProofSharing.c358 Gram663ProofSharing.c359)

noncomputable def Gram663ProofSharing.c362 := (Enclosure.Complex.inv_re_eq_mul Gram663ProofSharing.c50)

noncomputable def Gram663ProofSharing.c363 := (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) (Gram663ProofSharing.c50 : ℂ).re (Gram663ProofSharing.c50 : ℂ).re)

noncomputable def Gram663ProofSharing.c364 := (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) (Gram663ProofSharing.c50 : ℂ).im (Gram663ProofSharing.c50 : ℂ).im)

noncomputable def Gram663ProofSharing.c365 := (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd) Gram663ProofSharing.c363 Gram663ProofSharing.c364)

noncomputable def Gram663ProofSharing.c366 := (Enclosure.Complex.normSq_eq_mul_add_mul Gram663ProofSharing.c50)

noncomputable def Gram663ProofSharing.c367 := (@Enclosure.Real.IsNear.mulLit_ff (Gram663ProofSharing.c50 : ℂ).re (Gram663ProofSharing.c50 : ℂ).re (nat_lit 100000) (nat_lit 400000) (nat_lit 0) (nat_lit 1) (nat_lit 100000) (nat_lit 400000) (nat_lit 0) (nat_lit 1) (nat_lit 1) (nat_lit 16) (nat_lit 0) (nat_lit 1) Gram663ProofSharing.c65 Gram663ProofSharing.c65 (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram663ProofSharing.c368 := (@Enclosure.Real.IsNear.mulLit_ff (Gram663ProofSharing.c50 : ℂ).im (Gram663ProofSharing.c50 : ℂ).im (nat_lit 203805970) (nat_lit 400000) (nat_lit 0) (nat_lit 1) (nat_lit 203805970) (nat_lit 400000) (nat_lit 0) (nat_lit 1) (nat_lit 415368734076409) (nat_lit 1600000000) (nat_lit 0) (nat_lit 1) Gram663ProofSharing.c68 Gram663ProofSharing.c68 (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram663ProofSharing.c369 := (@Enclosure.Real.IsNear.addLit_ff Gram663ProofSharing.c363 Gram663ProofSharing.c364 (nat_lit 1) (nat_lit 16) (nat_lit 0) (nat_lit 1) (nat_lit 415368734076409) (nat_lit 1600000000) (nat_lit 0) (nat_lit 1) (nat_lit 6645901345222544) (nat_lit 415368834076409) (nat_lit 1600000000) (nat_lit 0) (nat_lit 1) Gram663ProofSharing.c367 Gram663ProofSharing.c368 (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram663ProofSharing.c370 := (@Neg.neg.{0} Real Real.instNeg (Gram663ProofSharing.c50 : ℂ).im)

noncomputable def Gram663ProofSharing.c371 := (Enclosure.Complex.inv_im_eq_mul Gram663ProofSharing.c50)

noncomputable def Gram663ProofSharing.c372 := (@Enclosure.Real.IsNear.neg (Gram663ProofSharing.c50 : ℂ).im Bool.false (nat_lit 203805970) (nat_lit 400000) (nat_lit 0) (nat_lit 1) Gram663ProofSharing.c68)

noncomputable def Gram663ProofSharing.c373 := (@Enclosure.Complex.IsNear.im_isNear Gram663ProofSharing.c343 Bool.false (nat_lit 1) (nat_lit 12) (nat_lit 0) (nat_lit 1) Bool.false (nat_lit 0) (nat_lit 1) (nat_lit 0) (nat_lit 1) Gram663ProofSharing.c354)

noncomputable def Gram663ProofSharing.c374 := (nat_lit 1980704062856608439838598758400000000)

noncomputable def Gram663ProofSharing.c375 := (BSN.stirling_coeff_mk (nat_lit 2) (nat_lit 1) (nat_lit 30) Bool.true BSN.bern_real_2 (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram663ProofSharing.c376 := (Enclosure.sfrac Bool.true (nat_lit 1) (nat_lit 360))

noncomputable def Gram663ProofSharing.c377 := (Enclosure.Real.IsNear.const Bool.true (nat_lit 1) (nat_lit 360))

noncomputable def Gram663ProofSharing.c378 := (@Enclosure.Complex.IsNear.mk Gram663ProofSharing.c376 Gram663ProofSharing.c302 Bool.true (nat_lit 1) (nat_lit 360) (nat_lit 0) (nat_lit 1) Bool.false (nat_lit 0) (nat_lit 1) (nat_lit 0) (nat_lit 1) Gram663ProofSharing.c377 Gram663ProofSharing.c303)

noncomputable def Gram663ProofSharing.c379 := (@Enclosure.Complex.IsNear.of_eq Gram663ProofSharing.c329 { re := Enclosure.sfrac Bool.true (nat_lit 1) (nat_lit 360), im := Enclosure.sfrac Bool.false (nat_lit 0) (nat_lit 1) } Bool.true (nat_lit 1) (nat_lit 360) (nat_lit 0) (nat_lit 1) Bool.false (nat_lit 0) (nat_lit 1) (nat_lit 0) (nat_lit 1) Gram663ProofSharing.c375 Gram663ProofSharing.c378)

noncomputable def Gram663ProofSharing.c380 := (@Enclosure.Complex.IsNear.re_isNear Gram663ProofSharing.c329 Bool.true (nat_lit 1) (nat_lit 360) (nat_lit 0) (nat_lit 1) Bool.false (nat_lit 0) (nat_lit 1) (nat_lit 0) (nat_lit 1) Gram663ProofSharing.c379)

noncomputable def Gram663ProofSharing.c381 := (nat_lit 19807040628566084398385987584000000000000)

noncomputable def Gram663ProofSharing.c382 := (@Inv.inv.{0} Complex Complex.instInv Gram663ProofSharing.c48)

noncomputable def Gram663ProofSharing.c383 := (BSN.zpow_one_sub_two_mul Gram663ProofSharing.c47 (nat_lit 2) (nat_lit 3) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram663ProofSharing.c384 := (Enclosure.Complex.inv_re_eq_mul Gram663ProofSharing.c48)

noncomputable def Gram663ProofSharing.c385 := (@Enclosure.Complex.IsNear.re_isNear Gram663ProofSharing.c48 Bool.true (nat_lit 1246106102229227) (nat_lit 6400000000) (nat_lit 0) (nat_lit 1) Bool.true (nat_lit 8465456661432359036173) (nat_lit 64000000000000) (nat_lit 0) (nat_lit 1) Zeta.Certificates.Gram.gp9_cert._proof_2)

noncomputable def Gram663ProofSharing.c386 := (nat_lit 71664111764631303578288553818168198422485929)

noncomputable def Gram663ProofSharing.c387 := (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) (Gram663ProofSharing.c48 : ℂ).re (Gram663ProofSharing.c48 : ℂ).re)

noncomputable def Gram663ProofSharing.c388 := (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) (Gram663ProofSharing.c48 : ℂ).im (Gram663ProofSharing.c48 : ℂ).im)

noncomputable def Gram663ProofSharing.c389 := (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd) Gram663ProofSharing.c387 Gram663ProofSharing.c388)

noncomputable def Gram663ProofSharing.c390 := (Enclosure.Complex.normSq_eq_mul_add_mul Gram663ProofSharing.c48)

noncomputable def Gram663ProofSharing.c391 := (nat_lit 1552780418012916730938853017529)

noncomputable def Gram663ProofSharing.c392 := (nat_lit 71663956486589502286615459932866445522485929)

noncomputable def Gram663ProofSharing.c393 := (nat_lit 2935362017879298194566699164392169407385023651840000000000000000)

noncomputable def Gram663ProofSharing.c394 := (@Enclosure.Real.IsNear.mulLit_tt (Gram663ProofSharing.c48 : ℂ).re (Gram663ProofSharing.c48 : ℂ).re (nat_lit 1246106102229227) (nat_lit 6400000000) (nat_lit 0) (nat_lit 1) (nat_lit 1246106102229227) (nat_lit 6400000000) (nat_lit 0) (nat_lit 1) Gram663ProofSharing.c391 (nat_lit 40960000000000000000) (nat_lit 0) (nat_lit 1) Gram663ProofSharing.c385 Gram663ProofSharing.c385 (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram663ProofSharing.c395 := (@Enclosure.Complex.IsNear.im_isNear Gram663ProofSharing.c48 Bool.true (nat_lit 1246106102229227) (nat_lit 6400000000) (nat_lit 0) (nat_lit 1) Bool.true (nat_lit 8465456661432359036173) (nat_lit 64000000000000) (nat_lit 0) (nat_lit 1) Zeta.Certificates.Gram.gp9_cert._proof_2)

noncomputable def Gram663ProofSharing.c396 := (@Enclosure.Real.IsNear.mulLit_tt (Gram663ProofSharing.c48 : ℂ).im (Gram663ProofSharing.c48 : ℂ).im (nat_lit 8465456661432359036173) (nat_lit 64000000000000) (nat_lit 0) (nat_lit 1) (nat_lit 8465456661432359036173) (nat_lit 64000000000000) (nat_lit 0) (nat_lit 1) Gram663ProofSharing.c392 (nat_lit 4096000000000000000000000000) (nat_lit 0) (nat_lit 1) Gram663ProofSharing.c395 Gram663ProofSharing.c395 (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram663ProofSharing.c397 := (@Enclosure.Real.IsNear.addLit_ff Gram663ProofSharing.c387 Gram663ProofSharing.c388 Gram663ProofSharing.c391 (nat_lit 40960000000000000000) (nat_lit 0) (nat_lit 1) Gram663ProofSharing.c392 (nat_lit 4096000000000000000000000000) (nat_lit 0) (nat_lit 1) Gram663ProofSharing.c393 Gram663ProofSharing.c386 (nat_lit 4096000000000000000000000000) (nat_lit 0) (nat_lit 1) Gram663ProofSharing.c394 Gram663ProofSharing.c396 (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram663ProofSharing.c398 := (@Neg.neg.{0} Real Real.instNeg (Gram663ProofSharing.c48 : ℂ).im)

noncomputable def Gram663ProofSharing.c399 := (Enclosure.Complex.inv_im_eq_mul Gram663ProofSharing.c48)

noncomputable def Gram663ProofSharing.c400 := (@Enclosure.Real.IsNear.neg (Gram663ProofSharing.c48 : ℂ).im Bool.true (nat_lit 8465456661432359036173) (nat_lit 64000000000000) (nat_lit 0) (nat_lit 1) Gram663ProofSharing.c395)

noncomputable def Gram663ProofSharing.c401 := (@Enclosure.Complex.IsNear.im_isNear Gram663ProofSharing.c329 Bool.true (nat_lit 1) (nat_lit 360) (nat_lit 0) (nat_lit 1) Bool.false (nat_lit 0) (nat_lit 1) (nat_lit 0) (nat_lit 1) Gram663ProofSharing.c379)

noncomputable def Gram663ProofSharing.c402 := (BSN.logSumC Gram663ProofSharing.c39 (nat_lit 0))

noncomputable def Gram663ProofSharing.c403 := (Enclosure.sfrac Bool.false (nat_lit 98304000000000000000000000) Gram663ProofSharing.c106)

noncomputable def Gram663ProofSharing.c404 := (@Monoid.toNPow.{0} Real Real.instMonoid)

noncomputable def Gram663ProofSharing.c405 := (@NPow.toPow.{0} Real Gram663ProofSharing.c404)

noncomputable def Gram663ProofSharing.c406 := (@instHPow.{0, 0} Real Nat Gram663ProofSharing.c405)

noncomputable def Gram663ProofSharing.c407 := (@HPow.hPow.{0, 0, 0} Real Nat Real Gram663ProofSharing.c406 Gram663ProofSharing.c7 (nat_lit 4))

noncomputable def Gram663ProofSharing.c408 := (@Inv.inv.{0} Real Real.instInv Gram663ProofSharing.c407)

noncomputable def Gram663ProofSharing.c409 := (nat_lit 611446774371975769155682509262542103857872115376664175900625)

noncomputable def Gram663ProofSharing.c410 := (nat_lit 392318858461667547739736838950479151006397215279002157056)

noncomputable def Gram663ProofSharing.c411 := (nat_lit 19652562622312316682495810535216024035134795670488584765154486969712234385047)

noncomputable def Gram663ProofSharing.c412 := (nat_lit 9903520314283042199192993792000000000000000000000000000000000000000000000000000000000000)

noncomputable def Gram663ProofSharing.c413 := (@HPow.hPow.{0, 0, 0} Real Nat Real Gram663ProofSharing.c406 Gram663ProofSharing.c7 (nat_lit 3))

noncomputable def Gram663ProofSharing.c414 := (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) Gram663ProofSharing.c413 Gram663ProofSharing.c7)

noncomputable def Gram663ProofSharing.c415 := (BSN.pow_succ_r Gram663ProofSharing.c7 (nat_lit 3) (nat_lit 4) (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram663ProofSharing.c416 := (nat_lit 691463075802508163054686763366652189853178875)

noncomputable def Gram663ProofSharing.c417 := (nat_lit 2787593149816327892691964784081045188247552)

noncomputable def Gram663ProofSharing.c418 := (nat_lit 2184744797947834540264818678394244808492865883128339)

noncomputable def Gram663ProofSharing.c419 := (nat_lit 9223372036854775808000000000000000000000000000000000000000000000)

noncomputable def Gram663ProofSharing.c420 := (@HPow.hPow.{0, 0, 0} Real Nat Real Gram663ProofSharing.c406 Gram663ProofSharing.c7 (nat_lit 2))

noncomputable def Gram663ProofSharing.c421 := (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) Gram663ProofSharing.c420 Gram663ProofSharing.c7)

noncomputable def Gram663ProofSharing.c422 := (BSN.pow_succ_r Gram663ProofSharing.c7 (nat_lit 2) (nat_lit 3) (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram663ProofSharing.c423 := (nat_lit 1073741824000000000000000000000000000000)

noncomputable def Gram663ProofSharing.c424 := (@HPow.hPow.{0, 0, 0} Real Nat Real Gram663ProofSharing.c406 Gram663ProofSharing.c7 (nat_lit 1))

noncomputable def Gram663ProofSharing.c425 := (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) Gram663ProofSharing.c424 Gram663ProofSharing.c7)

noncomputable def Gram663ProofSharing.c426 := (BSN.pow_succ_r Gram663ProofSharing.c7 (nat_lit 1) (nat_lit 2) (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram663ProofSharing.c427 := (BSN.pow_one_r Gram663ProofSharing.c7)

noncomputable def Gram663ProofSharing.c428 := (@Enclosure.Real.IsNear.of_eq Gram663ProofSharing.c7 Gram663ProofSharing.c10 Bool.false (nat_lit 884279719003555) (nat_lit 140737488355328) (nat_lit 1) (nat_lit 500000000000000) BSN.two_pi_eq Gram663ProofSharing.c13)

noncomputable def Gram663ProofSharing.c429 := (@Enclosure.Real.IsNear.of_eq Gram663ProofSharing.c424 Gram663ProofSharing.c7 Bool.false (nat_lit 884279719003555) (nat_lit 140737488355328) (nat_lit 1) (nat_lit 500000000000000) Gram663ProofSharing.c427 Gram663ProofSharing.c428)

noncomputable def Gram663ProofSharing.c430 := (@Enclosure.Real.IsNear.mulLit_ff Gram663ProofSharing.c424 Gram663ProofSharing.c7 (nat_lit 884279719003555) (nat_lit 140737488355328) (nat_lit 1) (nat_lit 500000000000000) (nat_lit 884279719003555) (nat_lit 140737488355328) (nat_lit 1) (nat_lit 500000000000000) (nat_lit 781950621441006189802102638025) (nat_lit 19807040628566084398385987584) (nat_lit 26986075409044041160201671) Gram663ProofSharing.c423 Gram663ProofSharing.c429 Gram663ProofSharing.c428 (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram663ProofSharing.c431 := (@Enclosure.Real.IsNear.of_eq Gram663ProofSharing.c420 Gram663ProofSharing.c425 Bool.false (nat_lit 781950621441006189802102638025) (nat_lit 19807040628566084398385987584) (nat_lit 26986075409044041160201671) Gram663ProofSharing.c423 Gram663ProofSharing.c426 Gram663ProofSharing.c430)

noncomputable def Gram663ProofSharing.c432 := (@Enclosure.Real.IsNear.mulLit_ff Gram663ProofSharing.c420 Gram663ProofSharing.c7 (nat_lit 781950621441006189802102638025) (nat_lit 19807040628566084398385987584) (nat_lit 26986075409044041160201671) Gram663ProofSharing.c423 (nat_lit 884279719003555) (nat_lit 140737488355328) (nat_lit 1) (nat_lit 500000000000000) Gram663ProofSharing.c416 Gram663ProofSharing.c417 Gram663ProofSharing.c418 Gram663ProofSharing.c419 Gram663ProofSharing.c431 Gram663ProofSharing.c428 (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram663ProofSharing.c433 := (@Enclosure.Real.IsNear.of_eq Gram663ProofSharing.c413 Gram663ProofSharing.c421 Bool.false Gram663ProofSharing.c416 Gram663ProofSharing.c417 Gram663ProofSharing.c418 Gram663ProofSharing.c419 Gram663ProofSharing.c422 Gram663ProofSharing.c432)

noncomputable def Gram663ProofSharing.c434 := (@Enclosure.Real.IsNear.mulLit_ff Gram663ProofSharing.c413 Gram663ProofSharing.c7 Gram663ProofSharing.c416 Gram663ProofSharing.c417 Gram663ProofSharing.c418 Gram663ProofSharing.c419 (nat_lit 884279719003555) (nat_lit 140737488355328) (nat_lit 1) (nat_lit 500000000000000) Gram663ProofSharing.c409 Gram663ProofSharing.c410 Gram663ProofSharing.c411 Gram663ProofSharing.c412 Gram663ProofSharing.c433 Gram663ProofSharing.c428 (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram663ProofSharing.c435 := (@Enclosure.Real.IsNear.of_eq Gram663ProofSharing.c407 Gram663ProofSharing.c414 Bool.false Gram663ProofSharing.c409 Gram663ProofSharing.c410 Gram663ProofSharing.c411 Gram663ProofSharing.c412 Gram663ProofSharing.c415 Gram663ProofSharing.c434)

noncomputable def Gram663ProofSharing.c436 := (@Enclosure.Real.IsNear.inv_image Gram663ProofSharing.c407 Gram663ProofSharing.c409 Gram663ProofSharing.c410 Gram663ProofSharing.c411 Gram663ProofSharing.c412 (nat_lit 5511507) (nat_lit 5511508) (nat_lit 8589934592) Gram663ProofSharing.c435 (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram663ProofSharing.c437 := (@Enclosure.Real.IsNear.recentre' Gram663ProofSharing.c408 Bool.false (nat_lit 11023015) (nat_lit 17179869184) (nat_lit 1) (nat_lit 17179869184) (nat_lit 11023015) (nat_lit 17179869184) (nat_lit 1) (nat_lit 17179869184) Gram663ProofSharing.c436 (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram663ProofSharing.c438 := (nat_lit 704313932278851456004411460141381886199)

noncomputable def Gram663ProofSharing.c439 := (nat_lit 13926825441960528092615147520000000000000000)

noncomputable def Gram663ProofSharing.c440 := (nat_lit 15058424344081598300326905737659573882633)

noncomputable def Gram663ProofSharing.c441 := (nat_lit 95746924913478630636729139200000000000000000000)

noncomputable def Gram663ProofSharing.c442 := (nat_lit 1725312886391118404873872359755776)

noncomputable def Gram663ProofSharing.c443 := (riemannSiegelThetaApproximant (nat_lit 2) (nat_lit 0) Gram663ProofSharing.c107)

noncomputable def Gram663ProofSharing.c444 := (nat_lit 29007850189354612506874943697211460141381886199)

noncomputable def Gram663ProofSharing.c445 := (nat_lit 15058360863870380663994793586240284282633)

noncomputable def Gram663ProofSharing.c446 := (Complex.Stirling.logGammaStirling (nat_lit 2) Gram663ProofSharing.c112)

noncomputable def Gram663ProofSharing.c447 := (@HDiv.hDiv.{0, 0, 0} Real Real Real Gram663ProofSharing.c15 Gram663ProofSharing.c107 Gram663ProofSharing.c6)

noncomputable def Gram663ProofSharing.c448 := (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) Gram663ProofSharing.c447 (Real.log Real.pi))

noncomputable def Gram663ProofSharing.c449 := (nat_lit 37130768324363826158863899175676381741381886199)

noncomputable def Gram663ProofSharing.c450 := (nat_lit 3699836958948062559304105586240284282633)

noncomputable def Gram663ProofSharing.c451 := (nat_lit 892412727319936173485629727500681479326551)

noncomputable def Gram663ProofSharing.c452 := (nat_lit 1114146035356842247409211801600000000000)

noncomputable def Gram663ProofSharing.c453 := (nat_lit 1851143397825358138721204530460680995581)

noncomputable def Gram663ProofSharing.c454 := (nat_lit 23936731228369657659182284800000000000000000000)

noncomputable def Gram663ProofSharing.c455 := (@HSub.hSub.{0, 0, 0} Complex Complex Complex (@instHSub.{0} Complex Complex.instSub) Gram663ProofSharing.c112 Gram663ProofSharing.c233)

noncomputable def Gram663ProofSharing.c456 := (Complex.log Gram663ProofSharing.c112)

noncomputable def Gram663ProofSharing.c457 := (@HMul.hMul.{0, 0, 0} Complex Complex Complex (@instHMul.{0} Complex Complex.instMul) Gram663ProofSharing.c455 Gram663ProofSharing.c456)

noncomputable def Gram663ProofSharing.c458 := (@HSub.hSub.{0, 0, 0} Complex Complex Complex (@instHSub.{0} Complex Complex.instSub) Gram663ProofSharing.c457 Gram663ProofSharing.c112)

noncomputable def Gram663ProofSharing.c459 := (@HAdd.hAdd.{0, 0, 0} Complex Complex Complex (@instHAdd.{0} Complex Complex.instAdd) Gram663ProofSharing.c458 Gram663ProofSharing.c238)

noncomputable def Gram663ProofSharing.c460 := (nat_lit 89410206662547540019232504673449)

noncomputable def Gram663ProofSharing.c461 := (nat_lit 2277791219216373704853820962258618113801)

noncomputable def Gram663ProofSharing.c462 := (BSN.w_sub_half_zero_mk Gram663ProofSharing.c107 Bool.false (nat_lit 101902988) (nat_lit 100000) Gram663ProofSharing.c121 (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram663ProofSharing.c463 := (@Enclosure.Complex.IsNear.mk Gram663ProofSharing.c248 Gram663ProofSharing.c123 Bool.true (nat_lit 100000) (nat_lit 400000) (nat_lit 0) (nat_lit 1) Bool.false (nat_lit 203805976) (nat_lit 400000) (nat_lit 0) (nat_lit 1) Gram663ProofSharing.c249 Gram663ProofSharing.c124)

noncomputable def Gram663ProofSharing.c464 := (@Enclosure.Complex.IsNear.of_eq Gram663ProofSharing.c455 { re := Enclosure.sfrac Bool.true (nat_lit 100000) (nat_lit 400000), im := Enclosure.sfrac Bool.false (nat_lit 203805976) (nat_lit 400000) } Bool.true (nat_lit 100000) (nat_lit 400000) (nat_lit 0) (nat_lit 1) Bool.false (nat_lit 203805976) (nat_lit 400000) (nat_lit 0) (nat_lit 1) Gram663ProofSharing.c462 Gram663ProofSharing.c463)

noncomputable def Gram663ProofSharing.c465 := (@Enclosure.Complex.IsNear.re_isNear Gram663ProofSharing.c455 Bool.true (nat_lit 100000) (nat_lit 400000) (nat_lit 0) (nat_lit 1) Bool.false (nat_lit 203805976) (nat_lit 400000) (nat_lit 0) (nat_lit 1) Gram663ProofSharing.c464)

noncomputable def Gram663ProofSharing.c466 := (Complex.log { re := Enclosure.sfrac Bool.false (nat_lit 100000) (nat_lit 400000), im := Enclosure.sfrac Bool.false (nat_lit 203805976) (nat_lit 400000) })

noncomputable def Gram663ProofSharing.c467 := (@congrArg.{1, 1} Complex Complex Gram663ProofSharing.c112 { re := Enclosure.sfrac Bool.false (nat_lit 100000) (nat_lit 400000), im := Enclosure.sfrac Bool.false (nat_lit 203805976) (nat_lit 400000) } Complex.log Gram663ProofSharing.c122)

noncomputable def Gram663ProofSharing.c468 := (Enclosure.sfrac Bool.false (nat_lit 41536885853312576) (nat_lit 160000000000))

noncomputable def Gram663ProofSharing.c469 := (Real.log Gram663ProofSharing.c468)

noncomputable def Gram663ProofSharing.c470 := (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) Gram663ProofSharing.c255 Gram663ProofSharing.c469)

noncomputable def Gram663ProofSharing.c471 := (Enclosure.clog_re_eq (nat_lit 100000) (nat_lit 203805976) (nat_lit 400000) (nat_lit 41536885853312576) (nat_lit 160000000000) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram663ProofSharing.c472 := (@Nat.cast.{0} Real Real.instNatCast (nat_lit 41536885853312576))

noncomputable def Gram663ProofSharing.c473 := (@HDiv.hDiv.{0, 0, 0} Real Real Real Gram663ProofSharing.c15 Gram663ProofSharing.c472 Gram663ProofSharing.c262)

noncomputable def Gram663ProofSharing.c474 := (Real.log Gram663ProofSharing.c473)

noncomputable def Gram663ProofSharing.c475 := (nat_lit 11403794627867736268694568652247409646737451117583765664564231326772380423143108970278140020898015311051985179819030758621914100615717804252497173481224055195393458967909907378244836212444089111622313300214854796354411646790790682720153030049814290275033189146941633395152988484122522994260463406347118123437667130165736240917307920331530515251200)

noncomputable def Gram663ProofSharing.c476 := (nat_lit 440435820559970576792774695016905307211957982858867786404640780929770890606497400818250624644961548535482819465615775251541262316959047105702122222065223201449011394470193021219269608390716177533613301573220459556572793360921318769624306962236882145456366475412029182528298478635452460821839110056719719728566177856441670214356619118900485816320)

noncomputable def Gram663ProofSharing.c477 := (nat_lit 119892060920461007782670712502805010786412444604863570947747813964543088164863481959173260160479486042143819795320506100069611602926157164747317812636184742524342499538648462676778500771356602622213958170743966914712034286645348386977473899567914405557998820085055862587850882487363752487624045732661732392719705342593388541501453107200)

noncomputable def Gram663ProofSharing.c478 := (BSN.artanhP (nat_lit 20565365853312576))

noncomputable def Gram663ProofSharing.c479 := (BSN.artanhQ (nat_lit 62508405853312576))

noncomputable def Gram663ProofSharing.c480 := (@BSN.binarySplit_of_base10 Gram663ProofSharing.c478 Gram663ProofSharing.c479 (nat_lit 0) (nat_lit 10) Gram663ProofSharing.c476 Gram663ProofSharing.c475 Gram663ProofSharing.c477 (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram663ProofSharing.c481 := (BSN.log_dyadic_bound (nat_lit 20565365853312576) (nat_lit 62508405853312576) (nat_lit 11) (nat_lit 10) Gram663ProofSharing.c475 (nat_lit 17179869184) (nat_lit 6600000000) Gram663ProofSharing.c476 Gram663ProofSharing.c477 (nat_lit 11741006436) (nat_lit 83073771706625152) (nat_lit 41943040000000000) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) Gram663ProofSharing.c480 (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram663ProofSharing.c482 := (BSN.log_rat_reduce_isNear (nat_lit 41536885853312576) (nat_lit 160000000000) (nat_lit 17) (nat_lit 83073771706625152) (nat_lit 41943040000000000) (nat_lit 11741006436) (nat_lit 17179869184) (nat_lit 24973259072661432) (nat_lit 36028797018963968) (nat_lit 6600000000) (nat_lit 1000000000000000) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) Gram663ProofSharing.c481 BSN.log2_near_15 (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram663ProofSharing.c483 := (@Enclosure.Real.IsNear.recentre' Gram663ProofSharing.c474 Bool.false (nat_lit 7716648845110890954535993344) (nat_lit 618970019642690137449562112) (nat_lit 1000112200000000) (nat_lit 6600000000000000000000000) (nat_lit 56146009920564327) (nat_lit 4503599627370496) (nat_lit 5000561) (nat_lit 33000000000000000) Gram663ProofSharing.c482 (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram663ProofSharing.c484 := (BSN.isNear_log_sfrac (nat_lit 41536885853312576) (nat_lit 160000000000) (nat_lit 56146009920564327) (nat_lit 4503599627370496) (nat_lit 5000561) (nat_lit 33000000000000000) Bool.false Gram663ProofSharing.c483)

noncomputable def Gram663ProofSharing.c485 := (@Enclosure.Real.IsNear.mulLit_ff Gram663ProofSharing.c255 Gram663ProofSharing.c469 (nat_lit 1) (nat_lit 2) (nat_lit 0) (nat_lit 1) (nat_lit 56146009920564327) (nat_lit 4503599627370496) (nat_lit 5000561) (nat_lit 33000000000000000) (nat_lit 56146009920564327) (nat_lit 9007199254740992) (nat_lit 5000561) (nat_lit 66000000000000000) Gram663ProofSharing.c260 Gram663ProofSharing.c484 (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram663ProofSharing.c486 := (@Enclosure.Real.IsNear.of_eq (Gram663ProofSharing.c466 : ℂ).re Gram663ProofSharing.c470 Bool.false (nat_lit 56146009920564327) (nat_lit 9007199254740992) (nat_lit 5000561) (nat_lit 66000000000000000) Gram663ProofSharing.c471 Gram663ProofSharing.c485)

noncomputable def Gram663ProofSharing.c487 := (@Nat.cast.{0} Real Real.instNatCast (nat_lit 203805976))

noncomputable def Gram663ProofSharing.c488 := (@HDiv.hDiv.{0, 0, 0} Real Real Real Gram663ProofSharing.c15 Gram663ProofSharing.c487 Gram663ProofSharing.c278)

noncomputable def Gram663ProofSharing.c489 := (Real.arctan Gram663ProofSharing.c488)

noncomputable def Gram663ProofSharing.c490 := (Enclosure.clog_im_eq (nat_lit 100000) (nat_lit 203805976) (nat_lit 400000) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram663ProofSharing.c491 := (@HDiv.hDiv.{0, 0, 0} Real Real Real Gram663ProofSharing.c15 Gram663ProofSharing.c278 Gram663ProofSharing.c487)

noncomputable def Gram663ProofSharing.c492 := (Real.arctan Gram663ProofSharing.c491)

noncomputable def Gram663ProofSharing.c493 := (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) Gram663ProofSharing.c282 Gram663ProofSharing.c492)

noncomputable def Gram663ProofSharing.c494 := (BSN.arctan_recip (nat_lit 203805976) (nat_lit 100000) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram663ProofSharing.c495 := (@BSN.binarySplit_of_le (BSN.arctanEvenP (nat_lit 100000)) (BSN.arctanEvenQ (nat_lit 203805976)) (nat_lit 0) (nat_lit 0) (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram663ProofSharing.c496 := (@BSN.binarySplit_of_le (BSN.arctanOddP (nat_lit 100000)) (BSN.arctanOddQ (nat_lit 203805976)) (nat_lit 0) (nat_lit 0) (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram663ProofSharing.c497 := (BSN.arctan_dyadic_bound_f (nat_lit 100000) (nat_lit 203805976) (nat_lit 1) (nat_lit 0) (nat_lit 17179869184) (nat_lit 6600000000) (nat_lit 0) (nat_lit 1) (nat_lit 1) (nat_lit 0) (nat_lit 1) (nat_lit 1) (nat_lit 8429521) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) Gram663ProofSharing.c495 Gram663ProofSharing.c496 (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram663ProofSharing.c498 := (@Enclosure.Real.IsNear.subLit_ff_p Gram663ProofSharing.c282 Gram663ProofSharing.c492 (nat_lit 884279719003555) (nat_lit 562949953421312) (nat_lit 1) (nat_lit 2000000000000000) (nat_lit 8429521) (nat_lit 17179869184) (nat_lit 1) (nat_lit 6600000000) (nat_lit 15187064496091039759597568) (nat_lit 884003500459427) (nat_lit 562949953421312) (nat_lit 10000033) (nat_lit 66000000000000000) Gram663ProofSharing.c287 Gram663ProofSharing.c497 (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram663ProofSharing.c499 := (@Enclosure.Real.IsNear.of_eq Gram663ProofSharing.c489 Gram663ProofSharing.c493 Bool.false (nat_lit 884003500459427) (nat_lit 562949953421312) (nat_lit 10000033) (nat_lit 66000000000000000) Gram663ProofSharing.c494 Gram663ProofSharing.c498)

noncomputable def Gram663ProofSharing.c500 := (@Enclosure.Real.IsNear.of_eq (Gram663ProofSharing.c466 : ℂ).im Gram663ProofSharing.c489 Bool.false (nat_lit 884003500459427) (nat_lit 562949953421312) (nat_lit 10000033) (nat_lit 66000000000000000) Gram663ProofSharing.c490 Gram663ProofSharing.c499)

noncomputable def Gram663ProofSharing.c501 := (@Enclosure.Complex.IsNear.of_parts Gram663ProofSharing.c466 Bool.false (nat_lit 56146009920564327) (nat_lit 9007199254740992) (nat_lit 5000561) (nat_lit 66000000000000000) Bool.false (nat_lit 884003500459427) (nat_lit 562949953421312) (nat_lit 10000033) (nat_lit 66000000000000000) Gram663ProofSharing.c486 Gram663ProofSharing.c500)

noncomputable def Gram663ProofSharing.c502 := (@Enclosure.Complex.IsNear.of_eq Gram663ProofSharing.c456 Gram663ProofSharing.c466 Bool.false (nat_lit 56146009920564327) (nat_lit 9007199254740992) (nat_lit 5000561) (nat_lit 66000000000000000) Bool.false (nat_lit 884003500459427) (nat_lit 562949953421312) (nat_lit 10000033) (nat_lit 66000000000000000) Gram663ProofSharing.c467 Gram663ProofSharing.c501)

noncomputable def Gram663ProofSharing.c503 := (@Enclosure.Complex.IsNear.re_isNear Gram663ProofSharing.c456 Bool.false (nat_lit 56146009920564327) (nat_lit 9007199254740992) (nat_lit 5000561) (nat_lit 66000000000000000) Bool.false (nat_lit 884003500459427) (nat_lit 562949953421312) (nat_lit 10000033) (nat_lit 66000000000000000) Gram663ProofSharing.c502)

noncomputable def Gram663ProofSharing.c504 := (@Enclosure.Complex.IsNear.im_isNear Gram663ProofSharing.c455 Bool.true (nat_lit 100000) (nat_lit 400000) (nat_lit 0) (nat_lit 1) Bool.false (nat_lit 203805976) (nat_lit 400000) (nat_lit 0) (nat_lit 1) Gram663ProofSharing.c464)

noncomputable def Gram663ProofSharing.c505 := (@Enclosure.Complex.IsNear.im_isNear Gram663ProofSharing.c456 Bool.false (nat_lit 56146009920564327) (nat_lit 9007199254740992) (nat_lit 5000561) (nat_lit 66000000000000000) Bool.false (nat_lit 884003500459427) (nat_lit 562949953421312) (nat_lit 10000033) (nat_lit 66000000000000000) Gram663ProofSharing.c502)

noncomputable def Gram663ProofSharing.c506 := (@HPow.hPow.{0, 0, 0} Complex Int Complex Gram663ProofSharing.c242 Gram663ProofSharing.c112 Gram663ProofSharing.c332)

noncomputable def Gram663ProofSharing.c507 := (@HMul.hMul.{0, 0, 0} Complex Complex Complex (@instHMul.{0} Complex Complex.instMul) Gram663ProofSharing.c329 Gram663ProofSharing.c506)

noncomputable def Gram663ProofSharing.c508 := (nat_lit 292467919253345198831058618113801)

noncomputable def Gram663ProofSharing.c509 := (@HPow.hPow.{0, 0, 0} Complex Int Complex Gram663ProofSharing.c242 Gram663ProofSharing.c112 Gram663ProofSharing.c346)

noncomputable def Gram663ProofSharing.c510 := (@HMul.hMul.{0, 0, 0} Complex Complex Complex (@instHMul.{0} Complex Complex.instMul) Gram663ProofSharing.c343 Gram663ProofSharing.c509)

noncomputable def Gram663ProofSharing.c511 := (@Inv.inv.{0} Complex Complex.instInv Gram663ProofSharing.c115)

noncomputable def Gram663ProofSharing.c512 := (BSN.zpow_one_sub_two_mul Gram663ProofSharing.c112 (nat_lit 1) (nat_lit 1) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram663ProofSharing.c513 := (Enclosure.Complex.inv_re_eq_mul Gram663ProofSharing.c115)

noncomputable def Gram663ProofSharing.c514 := (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) (Gram663ProofSharing.c115 : ℂ).re (Gram663ProofSharing.c115 : ℂ).re)

noncomputable def Gram663ProofSharing.c515 := (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) (Gram663ProofSharing.c115 : ℂ).im (Gram663ProofSharing.c115 : ℂ).im)

noncomputable def Gram663ProofSharing.c516 := (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd) Gram663ProofSharing.c514 Gram663ProofSharing.c515)

noncomputable def Gram663ProofSharing.c517 := (Enclosure.Complex.normSq_eq_mul_add_mul Gram663ProofSharing.c115)

noncomputable def Gram663ProofSharing.c518 := (@Enclosure.Real.IsNear.mulLit_ff (Gram663ProofSharing.c115 : ℂ).re (Gram663ProofSharing.c115 : ℂ).re (nat_lit 100000) (nat_lit 400000) (nat_lit 0) (nat_lit 1) (nat_lit 100000) (nat_lit 400000) (nat_lit 0) (nat_lit 1) (nat_lit 1) (nat_lit 16) (nat_lit 0) (nat_lit 1) Gram663ProofSharing.c128 Gram663ProofSharing.c128 (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram663ProofSharing.c519 := (@Enclosure.Real.IsNear.mulLit_ff (Gram663ProofSharing.c115 : ℂ).im (Gram663ProofSharing.c115 : ℂ).im (nat_lit 203805976) (nat_lit 400000) (nat_lit 0) (nat_lit 1) (nat_lit 203805976) (nat_lit 400000) (nat_lit 0) (nat_lit 1) (nat_lit 649013685208009) (nat_lit 2500000000) (nat_lit 0) (nat_lit 1) Gram663ProofSharing.c131 Gram663ProofSharing.c131 (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram663ProofSharing.c520 := (@Enclosure.Real.IsNear.addLit_ff Gram663ProofSharing.c514 Gram663ProofSharing.c515 (nat_lit 1) (nat_lit 16) (nat_lit 0) (nat_lit 1) (nat_lit 649013685208009) (nat_lit 2500000000) (nat_lit 0) (nat_lit 1) (nat_lit 10384221463328144) (nat_lit 649013841458009) (nat_lit 2500000000) (nat_lit 0) (nat_lit 1) Gram663ProofSharing.c518 Gram663ProofSharing.c519 (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram663ProofSharing.c521 := (@Neg.neg.{0} Real Real.instNeg (Gram663ProofSharing.c115 : ℂ).im)

noncomputable def Gram663ProofSharing.c522 := (Enclosure.Complex.inv_im_eq_mul Gram663ProofSharing.c115)

noncomputable def Gram663ProofSharing.c523 := (@Enclosure.Real.IsNear.neg (Gram663ProofSharing.c115 : ℂ).im Bool.false (nat_lit 203805976) (nat_lit 400000) (nat_lit 0) (nat_lit 1) Gram663ProofSharing.c131)

noncomputable def Gram663ProofSharing.c524 := (nat_lit 3094850098213450687247810560000000000)

noncomputable def Gram663ProofSharing.c525 := (nat_lit 38685626227668133590597632000000000000000)

noncomputable def Gram663ProofSharing.c526 := (@Inv.inv.{0} Complex Complex.instInv Gram663ProofSharing.c113)

noncomputable def Gram663ProofSharing.c527 := (BSN.zpow_one_sub_two_mul Gram663ProofSharing.c112 (nat_lit 2) (nat_lit 3) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram663ProofSharing.c528 := (Enclosure.Complex.inv_re_eq_mul Gram663ProofSharing.c113)

noncomputable def Gram663ProofSharing.c529 := (@Enclosure.Complex.IsNear.re_isNear Gram663ProofSharing.c113 Bool.true (nat_lit 1947040899374027) (nat_lit 10000000000) (nat_lit 0) (nat_lit 1) Bool.true (nat_lit 16534096502140473407723) (nat_lit 125000000000000) (nat_lit 0) (nat_lit 1) Zeta.Certificates.Gram.gp9_cert._proof_6)

noncomputable def Gram663ProofSharing.c530 := (nat_lit 273376939480885062015648137267262551102294729)

noncomputable def Gram663ProofSharing.c531 := (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) (Gram663ProofSharing.c113 : ℂ).re (Gram663ProofSharing.c113 : ℂ).re)

noncomputable def Gram663ProofSharing.c532 := (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) (Gram663ProofSharing.c113 : ℂ).im (Gram663ProofSharing.c113 : ℂ).im)

noncomputable def Gram663ProofSharing.c533 := (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd) Gram663ProofSharing.c531 Gram663ProofSharing.c532)

noncomputable def Gram663ProofSharing.c534 := (Enclosure.Complex.normSq_eq_mul_add_mul Gram663ProofSharing.c113)

noncomputable def Gram663ProofSharing.c535 := (nat_lit 3790968263835219933800442196729)

noncomputable def Gram663ProofSharing.c536 := (nat_lit 273376347142093837762533480948169312196044729)

noncomputable def Gram663ProofSharing.c537 := (nat_lit 27337693948088506201564813726726255110229472900000000000000000000)

noncomputable def Gram663ProofSharing.c538 := (@Enclosure.Real.IsNear.mulLit_tt (Gram663ProofSharing.c113 : ℂ).re (Gram663ProofSharing.c113 : ℂ).re (nat_lit 1947040899374027) (nat_lit 10000000000) (nat_lit 0) (nat_lit 1) (nat_lit 1947040899374027) (nat_lit 10000000000) (nat_lit 0) (nat_lit 1) Gram663ProofSharing.c535 (nat_lit 100000000000000000000) (nat_lit 0) (nat_lit 1) Gram663ProofSharing.c529 Gram663ProofSharing.c529 (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram663ProofSharing.c539 := (@Enclosure.Complex.IsNear.im_isNear Gram663ProofSharing.c113 Bool.true (nat_lit 1947040899374027) (nat_lit 10000000000) (nat_lit 0) (nat_lit 1) Bool.true (nat_lit 16534096502140473407723) (nat_lit 125000000000000) (nat_lit 0) (nat_lit 1) Zeta.Certificates.Gram.gp9_cert._proof_6)

noncomputable def Gram663ProofSharing.c540 := (@Enclosure.Real.IsNear.mulLit_tt (Gram663ProofSharing.c113 : ℂ).im (Gram663ProofSharing.c113 : ℂ).im (nat_lit 16534096502140473407723) (nat_lit 125000000000000) (nat_lit 0) (nat_lit 1) (nat_lit 16534096502140473407723) (nat_lit 125000000000000) (nat_lit 0) (nat_lit 1) Gram663ProofSharing.c536 (nat_lit 15625000000000000000000000000) (nat_lit 0) (nat_lit 1) Gram663ProofSharing.c539 Gram663ProofSharing.c539 (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram663ProofSharing.c541 := (@Enclosure.Real.IsNear.addLit_ff Gram663ProofSharing.c531 Gram663ProofSharing.c532 Gram663ProofSharing.c535 (nat_lit 100000000000000000000) (nat_lit 0) (nat_lit 1) Gram663ProofSharing.c536 (nat_lit 15625000000000000000000000000) (nat_lit 0) (nat_lit 1) Gram663ProofSharing.c537 Gram663ProofSharing.c530 (nat_lit 15625000000000000000000000000) (nat_lit 0) (nat_lit 1) Gram663ProofSharing.c538 Gram663ProofSharing.c540 (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram663ProofSharing.c542 := (@Neg.neg.{0} Real Real.instNeg (Gram663ProofSharing.c113 : ℂ).im)

noncomputable def Gram663ProofSharing.c543 := (Enclosure.Complex.inv_im_eq_mul Gram663ProofSharing.c113)

noncomputable def Gram663ProofSharing.c544 := (@Enclosure.Real.IsNear.neg (Gram663ProofSharing.c113 : ℂ).im Bool.true (nat_lit 16534096502140473407723) (nat_lit 125000000000000) (nat_lit 0) (nat_lit 1) Gram663ProofSharing.c539)

noncomputable def Gram663ProofSharing.c545 := (BSN.logSumC Gram663ProofSharing.c107 (nat_lit 0))

noncomputable def Gram663ProofSharing.c546 := (Enclosure.sfrac Bool.false (nat_lit 98304000000000000000000000) Gram663ProofSharing.c144)


