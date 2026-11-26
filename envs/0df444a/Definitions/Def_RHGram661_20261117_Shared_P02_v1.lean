-- Prove2me | Definitions.Def_RHGram661_20261117_Shared_P02_v1
-- name    : RHGram661_20261117_Shared_P02_v1
-- status  : Definition
-- author  : @bueno_ricardo
-- created : 2026-11-17T23:17:17.037202+00:00
-- url     : https://prove2.me/theorems/92a35b36-3423-4f1f-847a-9cf5dbbe9541
-- title:
--   Gram 661 ordinary shared terms, part 2
-- statement:
--   Exact shared expressions and complete ordinary auxiliary proofs for the endpoint certificate of Gram point 661. No additional axioms or custom proof generators. Imports the already published analytic and numerical support modules.
-- source:
--   Salvatore Mercuri and Bhavik Mehta, smmercuri/zeta commit 3dab6480a82f1bfc5de0a59550e279cf50490033; Apache-2.0. Ordinary proof export and exact sharing by Desenvolvimento RH. Full expanded strict AXLE and cumulative prefixes: daeae1c0-f53b-48d1-a4ac-c7223e87ecf0.

import Definitions.Def_RHGram661_20261117_Shared_P01_v1
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
noncomputable def Gram661ProofSharing.c225 := (@HDiv.hDiv.{0, 0, 0} Real Real Real Gram661ProofSharing.c15 Gram661ProofSharing.c39 Gram661ProofSharing.c6)

noncomputable def Gram661ProofSharing.c226 := (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) Gram661ProofSharing.c225 (Real.log Real.pi))

noncomputable def Gram661ProofSharing.c227 := (nat_lit 296188580223019650809827417043198064745222969)

noncomputable def Gram661ProofSharing.c228 := (nat_lit 738175504231706824495065830786022733661)

noncomputable def Gram661ProofSharing.c229 := (nat_lit 35610024486921321403287221993870535751493)

noncomputable def Gram661ProofSharing.c230 := (nat_lit 44565841414273689896368472064000000000)

noncomputable def Gram661ProofSharing.c231 := (nat_lit 369332833562235463105607889343157047177)

noncomputable def Gram661ProofSharing.c232 := (nat_lit 4787346245673931531836456960000000000000000000)

noncomputable def Gram661ProofSharing.c233 := (@HDiv.hDiv.{0, 0, 0} Complex Complex Complex Gram661ProofSharing.c28 Gram661ProofSharing.c30 Gram661ProofSharing.c42)

noncomputable def Gram661ProofSharing.c234 := (@HSub.hSub.{0, 0, 0} Complex Complex Complex (@instHSub.{0} Complex Complex.instSub) Gram661ProofSharing.c47 Gram661ProofSharing.c233)

noncomputable def Gram661ProofSharing.c235 := (Complex.log Gram661ProofSharing.c47)

noncomputable def Gram661ProofSharing.c236 := (@HMul.hMul.{0, 0, 0} Complex Complex Complex (@instHMul.{0} Complex Complex.instMul) Gram661ProofSharing.c234 Gram661ProofSharing.c235)

noncomputable def Gram661ProofSharing.c237 := (@HSub.hSub.{0, 0, 0} Complex Complex Complex (@instHSub.{0} Complex Complex.instSub) Gram661ProofSharing.c236 Gram661ProofSharing.c47)

noncomputable def Gram661ProofSharing.c238 := (@HMul.hMul.{0, 0, 0} Complex Complex Complex (@instHMul.{0} Complex Complex.instMul) Gram661ProofSharing.c233 ↑Gram661ProofSharing.c8)

noncomputable def Gram661ProofSharing.c239 := (@HAdd.hAdd.{0, 0, 0} Complex Complex Complex (@instHAdd.{0} Complex Complex.instAdd) Gram661ProofSharing.c237 Gram661ProofSharing.c238)

noncomputable def Gram661ProofSharing.c240 := (@DivInvMonoid.toZPow.{0} Complex Complex.instDivInvMonoid)

noncomputable def Gram661ProofSharing.c241 := (@ZPow.toPow.{0} Complex Gram661ProofSharing.c240)

noncomputable def Gram661ProofSharing.c242 := (@instHPow.{0, 0} Complex Int Gram661ProofSharing.c241)

noncomputable def Gram661ProofSharing.c243 := (@OfNat.ofNat.{0} Int (nat_lit 1) (@instOfNat (nat_lit 1)))

noncomputable def Gram661ProofSharing.c244 := (@OfNat.ofNat.{0} Int (nat_lit 2) (@instOfNat (nat_lit 2)))

noncomputable def Gram661ProofSharing.c245 := (nat_lit 3593809600936796179576837048507)

noncomputable def Gram661ProofSharing.c246 := (nat_lit 18266607132146514288323633039254777031)

noncomputable def Gram661ProofSharing.c247 := (BSN.w_sub_half_zero_mk Gram661ProofSharing.c39 Bool.false (nat_lit 101655980) (nat_lit 100000) Gram661ProofSharing.c56 (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram661ProofSharing.c248 := (Enclosure.sfrac Bool.true (nat_lit 100000) (nat_lit 400000))

noncomputable def Gram661ProofSharing.c249 := (Enclosure.Real.IsNear.const Bool.true (nat_lit 100000) (nat_lit 400000))

noncomputable def Gram661ProofSharing.c250 := (@Enclosure.Complex.IsNear.mk Gram661ProofSharing.c248 Gram661ProofSharing.c59 Bool.true (nat_lit 100000) (nat_lit 400000) (nat_lit 0) (nat_lit 1) Bool.false (nat_lit 203311960) (nat_lit 400000) (nat_lit 0) (nat_lit 1) Gram661ProofSharing.c249 Gram661ProofSharing.c61)

noncomputable def Gram661ProofSharing.c251 := (@Enclosure.Complex.IsNear.of_eq Gram661ProofSharing.c234 { re := Enclosure.sfrac Bool.true (nat_lit 100000) (nat_lit 400000), im := Enclosure.sfrac Bool.false (nat_lit 203311960) (nat_lit 400000) } Bool.true (nat_lit 100000) (nat_lit 400000) (nat_lit 0) (nat_lit 1) Bool.false (nat_lit 203311960) (nat_lit 400000) (nat_lit 0) (nat_lit 1) Gram661ProofSharing.c247 Gram661ProofSharing.c250)

noncomputable def Gram661ProofSharing.c252 := (@Enclosure.Complex.IsNear.re_isNear Gram661ProofSharing.c234 Bool.true (nat_lit 100000) (nat_lit 400000) (nat_lit 0) (nat_lit 1) Bool.false (nat_lit 203311960) (nat_lit 400000) (nat_lit 0) (nat_lit 1) Gram661ProofSharing.c251)

noncomputable def Gram661ProofSharing.c253 := (Complex.log { re := Enclosure.sfrac Bool.false (nat_lit 100000) (nat_lit 400000), im := Enclosure.sfrac Bool.false (nat_lit 203311960) (nat_lit 400000) })

noncomputable def Gram661ProofSharing.c254 := (@congrArg.{1, 1} Complex Complex Gram661ProofSharing.c47 { re := Enclosure.sfrac Bool.false (nat_lit 100000) (nat_lit 400000), im := Enclosure.sfrac Bool.false (nat_lit 203311960) (nat_lit 400000) } Complex.log Gram661ProofSharing.c57)

noncomputable def Gram661ProofSharing.c255 := (Enclosure.sfrac Bool.false (nat_lit 1) (nat_lit 2))

noncomputable def Gram661ProofSharing.c256 := (Enclosure.sfrac Bool.false (nat_lit 41335763079041600) (nat_lit 160000000000))

noncomputable def Gram661ProofSharing.c257 := (Real.log Gram661ProofSharing.c256)

noncomputable def Gram661ProofSharing.c258 := (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) Gram661ProofSharing.c255 Gram661ProofSharing.c257)

noncomputable def Gram661ProofSharing.c259 := (Enclosure.clog_re_eq (nat_lit 100000) (nat_lit 203311960) (nat_lit 400000) (nat_lit 41335763079041600) (nat_lit 160000000000) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram661ProofSharing.c260 := (Enclosure.Real.IsNear.const Bool.false (nat_lit 1) (nat_lit 2))

noncomputable def Gram661ProofSharing.c261 := (@Nat.cast.{0} Real Real.instNatCast (nat_lit 41335763079041600))

noncomputable def Gram661ProofSharing.c262 := (@Nat.cast.{0} Real Real.instNatCast (nat_lit 160000000000))

noncomputable def Gram661ProofSharing.c263 := (@HDiv.hDiv.{0, 0, 0} Real Real Real Gram661ProofSharing.c15 Gram661ProofSharing.c261 Gram661ProofSharing.c262)

noncomputable def Gram661ProofSharing.c264 := (Real.log Gram661ProofSharing.c263)

noncomputable def Gram661ProofSharing.c265 := (nat_lit 10691957051563849451062010517161480134697399189195260846065379025992214937777286205366222569381247473120576716888689641615319762138040982058459950597550250506789122359873763483060641828657178233893806049721422715509475826075125974202219467952853462317900975392093136923232274951710409499590838967821402112000000000000000000000000000000000000000000)

noncomputable def Gram661ProofSharing.c266 := (nat_lit 407142729841045313400995550803718046434571551736661052753039169028317724097802307071606039050725284299647922330612771976124634457085273294586298195640281510714817761934358678007024552621284040332074533530603649254372564138215358711162529808704777152772740966473356654531805105018391100771744896813052723200000000000000000000000000000000000000000)

noncomputable def Gram661ProofSharing.c267 := (nat_lit 98497923499578993574448675170327473449842334434345097814260465847748372969239919139002710718847813609782207002181720353765059469018588215295327692212334158375909367024337953748065656978639365022731690229201582219005872244502097333372470155872222137418930534584837608527916087082249005324828672000000000000000000000000000000000000000000)

noncomputable def Gram661ProofSharing.c268 := (BSN.artanhP (nat_lit 20364243079041600))

noncomputable def Gram661ProofSharing.c269 := (BSN.artanhQ (nat_lit 62307283079041600))

noncomputable def Gram661ProofSharing.c270 := (@BSN.binarySplit_of_base10 Gram661ProofSharing.c268 Gram661ProofSharing.c269 (nat_lit 0) (nat_lit 10) Gram661ProofSharing.c266 Gram661ProofSharing.c265 Gram661ProofSharing.c267 (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram661ProofSharing.c271 := (BSN.log_dyadic_bound (nat_lit 20364243079041600) (nat_lit 62307283079041600) (nat_lit 11) (nat_lit 10) Gram661ProofSharing.c265 (nat_lit 17179869184) (nat_lit 6600000000) Gram661ProofSharing.c266 Gram661ProofSharing.c267 (nat_lit 11657618979) (nat_lit 82671526158083200) (nat_lit 41943040000000000) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) Gram661ProofSharing.c270 (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram661ProofSharing.c272 := (BSN.log_rat_reduce_isNear (nat_lit 41335763079041600) (nat_lit 160000000000) (nat_lit 17) (nat_lit 82671526158083200) (nat_lit 41943040000000000) (nat_lit 11657618979) (nat_lit 17179869184) (nat_lit 24973259072661432) (nat_lit 36028797018963968) (nat_lit 6600000000) (nat_lit 1000000000000000) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) Gram661ProofSharing.c271 BSN.log2_near_15 (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram661ProofSharing.c273 := (@Enclosure.Real.IsNear.recentre' Gram661ProofSharing.c264 Bool.false (nat_lit 7713644495348710368469843968) (nat_lit 618970019642690137449562112) (nat_lit 1000112200000000) (nat_lit 6600000000000000000000000) (nat_lit 56124150399036519) (nat_lit 4503599627370496) (nat_lit 5000561) (nat_lit 33000000000000000) Gram661ProofSharing.c272 (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram661ProofSharing.c274 := (BSN.isNear_log_sfrac (nat_lit 41335763079041600) (nat_lit 160000000000) (nat_lit 56124150399036519) (nat_lit 4503599627370496) (nat_lit 5000561) (nat_lit 33000000000000000) Bool.false Gram661ProofSharing.c273)

noncomputable def Gram661ProofSharing.c275 := (@Enclosure.Real.IsNear.mulLit_ff Gram661ProofSharing.c255 Gram661ProofSharing.c257 (nat_lit 1) (nat_lit 2) (nat_lit 0) (nat_lit 1) (nat_lit 56124150399036519) (nat_lit 4503599627370496) (nat_lit 5000561) (nat_lit 33000000000000000) (nat_lit 56124150399036519) (nat_lit 9007199254740992) (nat_lit 5000561) (nat_lit 66000000000000000) Gram661ProofSharing.c260 Gram661ProofSharing.c274 (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram661ProofSharing.c276 := (@Enclosure.Real.IsNear.of_eq (Gram661ProofSharing.c253 : ℂ).re Gram661ProofSharing.c258 Bool.false (nat_lit 56124150399036519) (nat_lit 9007199254740992) (nat_lit 5000561) (nat_lit 66000000000000000) Gram661ProofSharing.c259 Gram661ProofSharing.c275)

noncomputable def Gram661ProofSharing.c277 := (@Nat.cast.{0} Real Real.instNatCast (nat_lit 203311960))

noncomputable def Gram661ProofSharing.c278 := (@Nat.cast.{0} Real Real.instNatCast (nat_lit 100000))

noncomputable def Gram661ProofSharing.c279 := (@HDiv.hDiv.{0, 0, 0} Real Real Real Gram661ProofSharing.c15 Gram661ProofSharing.c277 Gram661ProofSharing.c278)

noncomputable def Gram661ProofSharing.c280 := (Real.arctan Gram661ProofSharing.c279)

noncomputable def Gram661ProofSharing.c281 := (Enclosure.clog_im_eq (nat_lit 100000) (nat_lit 203311960) (nat_lit 400000) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram661ProofSharing.c282 := (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) Gram661ProofSharing.c255 Real.pi)

noncomputable def Gram661ProofSharing.c283 := (@HDiv.hDiv.{0, 0, 0} Real Real Real Gram661ProofSharing.c15 Gram661ProofSharing.c278 Gram661ProofSharing.c277)

noncomputable def Gram661ProofSharing.c284 := (Real.arctan Gram661ProofSharing.c283)

noncomputable def Gram661ProofSharing.c285 := (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) Gram661ProofSharing.c282 Gram661ProofSharing.c284)

noncomputable def Gram661ProofSharing.c286 := (BSN.arctan_recip (nat_lit 203311960) (nat_lit 100000) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram661ProofSharing.c287 := (@Enclosure.Real.IsNear.mulLit_ff Gram661ProofSharing.c255 Real.pi (nat_lit 1) (nat_lit 2) (nat_lit 0) (nat_lit 1) (nat_lit 226375608064910080) (nat_lit 72057594037927936) (nat_lit 1) (nat_lit 1000000000000000) (nat_lit 884279719003555) (nat_lit 562949953421312) (nat_lit 1) (nat_lit 2000000000000000) Gram661ProofSharing.c260 BSN.pi_near_15 (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram661ProofSharing.c288 := (@BSN.binarySplit_of_le (BSN.arctanEvenP (nat_lit 100000)) (BSN.arctanEvenQ (nat_lit 203311960)) (nat_lit 0) (nat_lit 0) (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram661ProofSharing.c289 := (@BSN.binarySplit_of_le (BSN.arctanOddP (nat_lit 100000)) (BSN.arctanOddQ (nat_lit 203311960)) (nat_lit 0) (nat_lit 0) (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram661ProofSharing.c290 := (BSN.arctan_dyadic_bound_f (nat_lit 100000) (nat_lit 203311960) (nat_lit 1) (nat_lit 0) (nat_lit 17179869184) (nat_lit 6600000000) (nat_lit 0) (nat_lit 1) (nat_lit 1) (nat_lit 0) (nat_lit 1) (nat_lit 1) (nat_lit 8450003) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) Gram661ProofSharing.c288 Gram661ProofSharing.c289 (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram661ProofSharing.c291 := (@Enclosure.Real.IsNear.subLit_ff_p Gram661ProofSharing.c282 Gram661ProofSharing.c284 (nat_lit 884279719003555) (nat_lit 562949953421312) (nat_lit 1) (nat_lit 2000000000000000) (nat_lit 8450003) (nat_lit 17179869184) (nat_lit 1) (nat_lit 6600000000) (nat_lit 15187052965750093784285184) (nat_lit 884002829305251) (nat_lit 562949953421312) (nat_lit 10000033) (nat_lit 66000000000000000) Gram661ProofSharing.c287 Gram661ProofSharing.c290 (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram661ProofSharing.c292 := (@Enclosure.Real.IsNear.of_eq Gram661ProofSharing.c280 Gram661ProofSharing.c285 Bool.false (nat_lit 884002829305251) (nat_lit 562949953421312) (nat_lit 10000033) (nat_lit 66000000000000000) Gram661ProofSharing.c286 Gram661ProofSharing.c291)

noncomputable def Gram661ProofSharing.c293 := (@Enclosure.Real.IsNear.of_eq (Gram661ProofSharing.c253 : ℂ).im Gram661ProofSharing.c280 Bool.false (nat_lit 884002829305251) (nat_lit 562949953421312) (nat_lit 10000033) (nat_lit 66000000000000000) Gram661ProofSharing.c281 Gram661ProofSharing.c292)

noncomputable def Gram661ProofSharing.c294 := (@Enclosure.Complex.IsNear.of_parts Gram661ProofSharing.c253 Bool.false (nat_lit 56124150399036519) (nat_lit 9007199254740992) (nat_lit 5000561) (nat_lit 66000000000000000) Bool.false (nat_lit 884002829305251) (nat_lit 562949953421312) (nat_lit 10000033) (nat_lit 66000000000000000) Gram661ProofSharing.c276 Gram661ProofSharing.c293)

noncomputable def Gram661ProofSharing.c295 := (@Enclosure.Complex.IsNear.of_eq Gram661ProofSharing.c235 Gram661ProofSharing.c253 Bool.false (nat_lit 56124150399036519) (nat_lit 9007199254740992) (nat_lit 5000561) (nat_lit 66000000000000000) Bool.false (nat_lit 884002829305251) (nat_lit 562949953421312) (nat_lit 10000033) (nat_lit 66000000000000000) Gram661ProofSharing.c254 Gram661ProofSharing.c294)

noncomputable def Gram661ProofSharing.c296 := (@Enclosure.Complex.IsNear.re_isNear Gram661ProofSharing.c235 Bool.false (nat_lit 56124150399036519) (nat_lit 9007199254740992) (nat_lit 5000561) (nat_lit 66000000000000000) Bool.false (nat_lit 884002829305251) (nat_lit 562949953421312) (nat_lit 10000033) (nat_lit 66000000000000000) Gram661ProofSharing.c295)

noncomputable def Gram661ProofSharing.c297 := (@Enclosure.Complex.IsNear.im_isNear Gram661ProofSharing.c234 Bool.true (nat_lit 100000) (nat_lit 400000) (nat_lit 0) (nat_lit 1) Bool.false (nat_lit 203311960) (nat_lit 400000) (nat_lit 0) (nat_lit 1) Gram661ProofSharing.c251)

noncomputable def Gram661ProofSharing.c298 := (@Enclosure.Complex.IsNear.im_isNear Gram661ProofSharing.c235 Bool.false (nat_lit 56124150399036519) (nat_lit 9007199254740992) (nat_lit 5000561) (nat_lit 66000000000000000) Bool.false (nat_lit 884002829305251) (nat_lit 562949953421312) (nat_lit 10000033) (nat_lit 66000000000000000) Gram661ProofSharing.c295)

noncomputable def Gram661ProofSharing.c299 := (↑Gram661ProofSharing.c8)

noncomputable def Gram661ProofSharing.c300 := (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) (Gram661ProofSharing.c233 : ℂ).re (Gram661ProofSharing.c299 : ℂ).re)

noncomputable def Gram661ProofSharing.c301 := (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) (Gram661ProofSharing.c233 : ℂ).im (Gram661ProofSharing.c299 : ℂ).im)

noncomputable def Gram661ProofSharing.c302 := (Enclosure.sfrac Bool.false (nat_lit 0) (nat_lit 1))

noncomputable def Gram661ProofSharing.c303 := (Enclosure.Real.IsNear.const Bool.false (nat_lit 0) (nat_lit 1))

noncomputable def Gram661ProofSharing.c304 := (@Enclosure.Complex.IsNear.mk Gram661ProofSharing.c255 Gram661ProofSharing.c302 Bool.false (nat_lit 1) (nat_lit 2) (nat_lit 0) (nat_lit 1) Bool.false (nat_lit 0) (nat_lit 1) (nat_lit 0) (nat_lit 1) Gram661ProofSharing.c260 Gram661ProofSharing.c303)

noncomputable def Gram661ProofSharing.c305 := (@Enclosure.Complex.IsNear.of_eq Gram661ProofSharing.c233 { re := Enclosure.sfrac Bool.false (nat_lit 1) (nat_lit 2), im := Enclosure.sfrac Bool.false (nat_lit 0) (nat_lit 1) } Bool.false (nat_lit 1) (nat_lit 2) (nat_lit 0) (nat_lit 1) Bool.false (nat_lit 0) (nat_lit 1) (nat_lit 0) (nat_lit 1) BSN.half_c_mk Gram661ProofSharing.c304)

noncomputable def Gram661ProofSharing.c306 := (@Enclosure.Complex.IsNear.re_isNear Gram661ProofSharing.c233 Bool.false (nat_lit 1) (nat_lit 2) (nat_lit 0) (nat_lit 1) Bool.false (nat_lit 0) (nat_lit 1) (nat_lit 0) (nat_lit 1) Gram661ProofSharing.c305)

noncomputable def Gram661ProofSharing.c307 := (Complex.ofReal_re Gram661ProofSharing.c8)

noncomputable def Gram661ProofSharing.c308 := (@Enclosure.Real.IsNear.of_eq (Gram661ProofSharing.c299 : ℂ).re Gram661ProofSharing.c8 Bool.false (nat_lit 3946810947) (nat_lit 2147483648) (nat_lit 1) (nat_lit 4294967296) Gram661ProofSharing.c307 Zeta.Certificates.Gram.gp7_cert._proof_1)

noncomputable def Gram661ProofSharing.c309 := (@Enclosure.Real.IsNear.mulLit_ff (Gram661ProofSharing.c233 : ℂ).re (Gram661ProofSharing.c299 : ℂ).re (nat_lit 1) (nat_lit 2) (nat_lit 0) (nat_lit 1) (nat_lit 3946810947) (nat_lit 2147483648) (nat_lit 1) (nat_lit 4294967296) (nat_lit 3946810947) (nat_lit 4294967296) (nat_lit 1) (nat_lit 8589934592) Gram661ProofSharing.c306 Gram661ProofSharing.c308 (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram661ProofSharing.c310 := (@Enclosure.Complex.IsNear.im_isNear Gram661ProofSharing.c233 Bool.false (nat_lit 1) (nat_lit 2) (nat_lit 0) (nat_lit 1) Bool.false (nat_lit 0) (nat_lit 1) (nat_lit 0) (nat_lit 1) Gram661ProofSharing.c305)

noncomputable def Gram661ProofSharing.c311 := (Complex.ofReal_im Gram661ProofSharing.c8)

noncomputable def Gram661ProofSharing.c312 := (@Eq.trans.{1} Real (Gram661ProofSharing.c299 : ℂ).im Gram661ProofSharing.c147 Gram661ProofSharing.c302 Gram661ProofSharing.c311 Enclosure.sfrac_zero_eq)

noncomputable def Gram661ProofSharing.c313 := (@Enclosure.Real.IsNear.of_eq (Gram661ProofSharing.c299 : ℂ).im Gram661ProofSharing.c302 Bool.false (nat_lit 0) (nat_lit 1) (nat_lit 0) (nat_lit 1) Gram661ProofSharing.c312 Gram661ProofSharing.c303)

noncomputable def Gram661ProofSharing.c314 := (@Enclosure.Real.IsNear.mulLit_ff (Gram661ProofSharing.c233 : ℂ).im (Gram661ProofSharing.c299 : ℂ).im (nat_lit 0) (nat_lit 1) (nat_lit 0) (nat_lit 1) (nat_lit 0) (nat_lit 1) (nat_lit 0) (nat_lit 1) (nat_lit 0) (nat_lit 1) (nat_lit 0) (nat_lit 1) Gram661ProofSharing.c310 Gram661ProofSharing.c313 (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram661ProofSharing.c315 := (@Enclosure.Real.IsNear.subLit_ff_p Gram661ProofSharing.c300 Gram661ProofSharing.c301 (nat_lit 3946810947) (nat_lit 4294967296) (nat_lit 1) (nat_lit 8589934592) (nat_lit 0) (nat_lit 1) (nat_lit 0) (nat_lit 1) (nat_lit 3946810947) (nat_lit 3946810947) (nat_lit 4294967296) (nat_lit 1) (nat_lit 8589934592) Gram661ProofSharing.c309 Gram661ProofSharing.c314 (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram661ProofSharing.c316 := (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) (Gram661ProofSharing.c233 : ℂ).re (Gram661ProofSharing.c299 : ℂ).im)

noncomputable def Gram661ProofSharing.c317 := (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) (Gram661ProofSharing.c233 : ℂ).im (Gram661ProofSharing.c299 : ℂ).re)

noncomputable def Gram661ProofSharing.c318 := (@Enclosure.Real.IsNear.mulLit_ff (Gram661ProofSharing.c233 : ℂ).re (Gram661ProofSharing.c299 : ℂ).im (nat_lit 1) (nat_lit 2) (nat_lit 0) (nat_lit 1) (nat_lit 0) (nat_lit 1) (nat_lit 0) (nat_lit 1) (nat_lit 0) (nat_lit 1) (nat_lit 0) (nat_lit 1) Gram661ProofSharing.c306 Gram661ProofSharing.c313 (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram661ProofSharing.c319 := (@Enclosure.Real.IsNear.mulLit_ff (Gram661ProofSharing.c233 : ℂ).im (Gram661ProofSharing.c299 : ℂ).re (nat_lit 0) (nat_lit 1) (nat_lit 0) (nat_lit 1) (nat_lit 3946810947) (nat_lit 2147483648) (nat_lit 1) (nat_lit 4294967296) (nat_lit 0) (nat_lit 1) (nat_lit 0) (nat_lit 1) Gram661ProofSharing.c310 Gram661ProofSharing.c308 (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram661ProofSharing.c320 := (@Enclosure.Real.IsNear.addLit_ff Gram661ProofSharing.c316 Gram661ProofSharing.c317 (nat_lit 0) (nat_lit 1) (nat_lit 0) (nat_lit 1) (nat_lit 0) (nat_lit 1) (nat_lit 0) (nat_lit 1) (nat_lit 0) (nat_lit 0) (nat_lit 1) (nat_lit 0) (nat_lit 1) Gram661ProofSharing.c318 Gram661ProofSharing.c319 (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram661ProofSharing.c321 := (@Enclosure.Complex.IsNear.mul Gram661ProofSharing.c233 Gram661ProofSharing.c299 Bool.false (nat_lit 3946810947) (nat_lit 4294967296) (nat_lit 1) (nat_lit 8589934592) Bool.false (nat_lit 0) (nat_lit 1) (nat_lit 0) (nat_lit 1) Gram661ProofSharing.c315 Gram661ProofSharing.c320)

noncomputable def Gram661ProofSharing.c322 := (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) Gram661ProofSharing.c32 (nat_lit 2))

noncomputable def Gram661ProofSharing.c323 := (bernoulli Gram661ProofSharing.c322)

noncomputable def Gram661ProofSharing.c324 := (@Rat.cast.{0} Complex Complex.instRatCast Gram661ProofSharing.c323)

noncomputable def Gram661ProofSharing.c325 := (@Nat.cast.{0} Complex Complex.instNatCast (nat_lit 2))

noncomputable def Gram661ProofSharing.c326 := (@HMul.hMul.{0, 0, 0} Complex Complex Complex (@instHMul.{0} Complex Complex.instMul) Gram661ProofSharing.c42 Gram661ProofSharing.c325)

noncomputable def Gram661ProofSharing.c327 := (@HSub.hSub.{0, 0, 0} Complex Complex Complex (@instHSub.{0} Complex Complex.instSub) Gram661ProofSharing.c326 Gram661ProofSharing.c30)

noncomputable def Gram661ProofSharing.c328 := (@HMul.hMul.{0, 0, 0} Complex Complex Complex (@instHMul.{0} Complex Complex.instMul) Gram661ProofSharing.c326 Gram661ProofSharing.c327)

noncomputable def Gram661ProofSharing.c329 := (@HDiv.hDiv.{0, 0, 0} Complex Complex Complex Gram661ProofSharing.c28 Gram661ProofSharing.c324 Gram661ProofSharing.c328)

noncomputable def Gram661ProofSharing.c330 := (@Nat.cast.{0} Int instNatCastInt (nat_lit 2))

noncomputable def Gram661ProofSharing.c331 := (@HMul.hMul.{0, 0, 0} Int Int Int (@instHMul.{0} Int Int.instMul) Gram661ProofSharing.c244 Gram661ProofSharing.c330)

noncomputable def Gram661ProofSharing.c332 := (@HSub.hSub.{0, 0, 0} Int Int Int (@instHSub.{0} Int Int.instSub) Gram661ProofSharing.c243 Gram661ProofSharing.c331)

noncomputable def Gram661ProofSharing.c333 := (@HPow.hPow.{0, 0, 0} Complex Int Complex Gram661ProofSharing.c242 Gram661ProofSharing.c47 Gram661ProofSharing.c332)

noncomputable def Gram661ProofSharing.c334 := (@HMul.hMul.{0, 0, 0} Complex Complex Complex (@instHMul.{0} Complex Complex.instMul) Gram661ProofSharing.c329 Gram661ProofSharing.c333)

noncomputable def Gram661ProofSharing.c335 := (nat_lit 2356840435516752830351254777031)

noncomputable def Gram661ProofSharing.c336 := (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) Gram661ProofSharing.c32 (nat_lit 1))

noncomputable def Gram661ProofSharing.c337 := (bernoulli Gram661ProofSharing.c336)

noncomputable def Gram661ProofSharing.c338 := (@Rat.cast.{0} Complex Complex.instRatCast Gram661ProofSharing.c337)

noncomputable def Gram661ProofSharing.c339 := (@Nat.cast.{0} Complex Complex.instNatCast (nat_lit 1))

noncomputable def Gram661ProofSharing.c340 := (@HMul.hMul.{0, 0, 0} Complex Complex Complex (@instHMul.{0} Complex Complex.instMul) Gram661ProofSharing.c42 Gram661ProofSharing.c339)

noncomputable def Gram661ProofSharing.c341 := (@HSub.hSub.{0, 0, 0} Complex Complex Complex (@instHSub.{0} Complex Complex.instSub) Gram661ProofSharing.c340 Gram661ProofSharing.c30)

noncomputable def Gram661ProofSharing.c342 := (@HMul.hMul.{0, 0, 0} Complex Complex Complex (@instHMul.{0} Complex Complex.instMul) Gram661ProofSharing.c340 Gram661ProofSharing.c341)

noncomputable def Gram661ProofSharing.c343 := (@HDiv.hDiv.{0, 0, 0} Complex Complex Complex Gram661ProofSharing.c28 Gram661ProofSharing.c338 Gram661ProofSharing.c342)

noncomputable def Gram661ProofSharing.c344 := (@Nat.cast.{0} Int instNatCastInt (nat_lit 1))

noncomputable def Gram661ProofSharing.c345 := (@HMul.hMul.{0, 0, 0} Int Int Int (@instHMul.{0} Int Int.instMul) Gram661ProofSharing.c244 Gram661ProofSharing.c344)

noncomputable def Gram661ProofSharing.c346 := (@HSub.hSub.{0, 0, 0} Int Int Int (@instHSub.{0} Int Int.instSub) Gram661ProofSharing.c243 Gram661ProofSharing.c345)

noncomputable def Gram661ProofSharing.c347 := (@HPow.hPow.{0, 0, 0} Complex Int Complex Gram661ProofSharing.c242 Gram661ProofSharing.c47 Gram661ProofSharing.c346)

noncomputable def Gram661ProofSharing.c348 := (@HMul.hMul.{0, 0, 0} Complex Complex Complex (@instHMul.{0} Complex Complex.instMul) Gram661ProofSharing.c343 Gram661ProofSharing.c347)

noncomputable def Gram661ProofSharing.c349 := (@Enclosure.Complex.IsNear.mk Gram661ProofSharing.c302 Gram661ProofSharing.c302 Bool.false (nat_lit 0) (nat_lit 1) (nat_lit 0) (nat_lit 1) Bool.false (nat_lit 0) (nat_lit 1) (nat_lit 0) (nat_lit 1) Gram661ProofSharing.c303 Gram661ProofSharing.c303)

noncomputable def Gram661ProofSharing.c350 := (BSN.stirling_coeff_mk (nat_lit 1) (nat_lit 1) (nat_lit 6) Bool.false BSN.bern_real_1 (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram661ProofSharing.c351 := (Enclosure.sfrac Bool.false (nat_lit 1) (nat_lit 12))

noncomputable def Gram661ProofSharing.c352 := (Enclosure.Real.IsNear.const Bool.false (nat_lit 1) (nat_lit 12))

noncomputable def Gram661ProofSharing.c353 := (@Enclosure.Complex.IsNear.mk Gram661ProofSharing.c351 Gram661ProofSharing.c302 Bool.false (nat_lit 1) (nat_lit 12) (nat_lit 0) (nat_lit 1) Bool.false (nat_lit 0) (nat_lit 1) (nat_lit 0) (nat_lit 1) Gram661ProofSharing.c352 Gram661ProofSharing.c303)

noncomputable def Gram661ProofSharing.c354 := (@Enclosure.Complex.IsNear.of_eq Gram661ProofSharing.c343 { re := Enclosure.sfrac Bool.false (nat_lit 1) (nat_lit 12), im := Enclosure.sfrac Bool.false (nat_lit 0) (nat_lit 1) } Bool.false (nat_lit 1) (nat_lit 12) (nat_lit 0) (nat_lit 1) Bool.false (nat_lit 0) (nat_lit 1) (nat_lit 0) (nat_lit 1) Gram661ProofSharing.c350 Gram661ProofSharing.c353)

noncomputable def Gram661ProofSharing.c355 := (@Enclosure.Complex.IsNear.re_isNear Gram661ProofSharing.c343 Bool.false (nat_lit 1) (nat_lit 12) (nat_lit 0) (nat_lit 1) Bool.false (nat_lit 0) (nat_lit 1) (nat_lit 0) (nat_lit 1) Gram661ProofSharing.c354)

noncomputable def Gram661ProofSharing.c356 := (@Inv.inv.{0} Complex Complex.instInv Gram661ProofSharing.c50)

noncomputable def Gram661ProofSharing.c357 := (BSN.zpow_one_sub_two_mul Gram661ProofSharing.c47 (nat_lit 1) (nat_lit 1) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram661ProofSharing.c358 := (@instMulZeroOneClassOfSemiring.{0} Complex Complex.instSemiring)

noncomputable def Gram661ProofSharing.c359 := (@instMulZeroOneClassOfSemiring.{0} Real Real.semiring)

noncomputable def Gram661ProofSharing.c360 := (@MonoidWithZeroHom.{0, 0} Complex Real Gram661ProofSharing.c358 Gram661ProofSharing.c359)

noncomputable def Gram661ProofSharing.c361 := (@MonoidWithZeroHom.funLike.{0, 0} Complex Real Gram661ProofSharing.c358 Gram661ProofSharing.c359)

noncomputable def Gram661ProofSharing.c362 := (Enclosure.Complex.inv_re_eq_mul Gram661ProofSharing.c50)

noncomputable def Gram661ProofSharing.c363 := (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) (Gram661ProofSharing.c50 : ℂ).re (Gram661ProofSharing.c50 : ℂ).re)

noncomputable def Gram661ProofSharing.c364 := (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) (Gram661ProofSharing.c50 : ℂ).im (Gram661ProofSharing.c50 : ℂ).im)

noncomputable def Gram661ProofSharing.c365 := (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd) Gram661ProofSharing.c363 Gram661ProofSharing.c364)

noncomputable def Gram661ProofSharing.c366 := (Enclosure.Complex.normSq_eq_mul_add_mul Gram661ProofSharing.c50)

noncomputable def Gram661ProofSharing.c367 := (@Enclosure.Real.IsNear.mulLit_ff (Gram661ProofSharing.c50 : ℂ).re (Gram661ProofSharing.c50 : ℂ).re (nat_lit 100000) (nat_lit 400000) (nat_lit 0) (nat_lit 1) (nat_lit 100000) (nat_lit 400000) (nat_lit 0) (nat_lit 1) (nat_lit 1) (nat_lit 16) (nat_lit 0) (nat_lit 1) Gram661ProofSharing.c65 Gram661ProofSharing.c65 (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram661ProofSharing.c368 := (@Enclosure.Real.IsNear.mulLit_ff (Gram661ProofSharing.c50 : ℂ).im (Gram661ProofSharing.c50 : ℂ).im (nat_lit 203311960) (nat_lit 400000) (nat_lit 0) (nat_lit 1) (nat_lit 203311960) (nat_lit 400000) (nat_lit 0) (nat_lit 1) (nat_lit 25834845674401) (nat_lit 100000000) (nat_lit 0) (nat_lit 1) Gram661ProofSharing.c68 Gram661ProofSharing.c68 (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram661ProofSharing.c369 := (@Enclosure.Real.IsNear.addLit_ff Gram661ProofSharing.c363 Gram661ProofSharing.c364 (nat_lit 1) (nat_lit 16) (nat_lit 0) (nat_lit 1) (nat_lit 25834845674401) (nat_lit 100000000) (nat_lit 0) (nat_lit 1) (nat_lit 413357630790416) (nat_lit 25834851924401) (nat_lit 100000000) (nat_lit 0) (nat_lit 1) Gram661ProofSharing.c367 Gram661ProofSharing.c368 (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram661ProofSharing.c370 := (@Neg.neg.{0} Real Real.instNeg (Gram661ProofSharing.c50 : ℂ).im)

noncomputable def Gram661ProofSharing.c371 := (Enclosure.Complex.inv_im_eq_mul Gram661ProofSharing.c50)

noncomputable def Gram661ProofSharing.c372 := (@Enclosure.Real.IsNear.neg (Gram661ProofSharing.c50 : ℂ).im Bool.false (nat_lit 203311960) (nat_lit 400000) (nat_lit 0) (nat_lit 1) Gram661ProofSharing.c68)

noncomputable def Gram661ProofSharing.c373 := (@Enclosure.Complex.IsNear.im_isNear Gram661ProofSharing.c343 Bool.false (nat_lit 1) (nat_lit 12) (nat_lit 0) (nat_lit 1) Bool.false (nat_lit 0) (nat_lit 1) (nat_lit 0) (nat_lit 1) Gram661ProofSharing.c354)

noncomputable def Gram661ProofSharing.c374 := (nat_lit 123794003928538027489912422400000000)

noncomputable def Gram661ProofSharing.c375 := (BSN.stirling_coeff_mk (nat_lit 2) (nat_lit 1) (nat_lit 30) Bool.true BSN.bern_real_2 (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram661ProofSharing.c376 := (Enclosure.sfrac Bool.true (nat_lit 1) (nat_lit 360))

noncomputable def Gram661ProofSharing.c377 := (Enclosure.Real.IsNear.const Bool.true (nat_lit 1) (nat_lit 360))

noncomputable def Gram661ProofSharing.c378 := (@Enclosure.Complex.IsNear.mk Gram661ProofSharing.c376 Gram661ProofSharing.c302 Bool.true (nat_lit 1) (nat_lit 360) (nat_lit 0) (nat_lit 1) Bool.false (nat_lit 0) (nat_lit 1) (nat_lit 0) (nat_lit 1) Gram661ProofSharing.c377 Gram661ProofSharing.c303)

noncomputable def Gram661ProofSharing.c379 := (@Enclosure.Complex.IsNear.of_eq Gram661ProofSharing.c329 { re := Enclosure.sfrac Bool.true (nat_lit 1) (nat_lit 360), im := Enclosure.sfrac Bool.false (nat_lit 0) (nat_lit 1) } Bool.true (nat_lit 1) (nat_lit 360) (nat_lit 0) (nat_lit 1) Bool.false (nat_lit 0) (nat_lit 1) (nat_lit 0) (nat_lit 1) Gram661ProofSharing.c375 Gram661ProofSharing.c378)

noncomputable def Gram661ProofSharing.c380 := (@Enclosure.Complex.IsNear.re_isNear Gram661ProofSharing.c329 Bool.true (nat_lit 1) (nat_lit 360) (nat_lit 0) (nat_lit 1) Bool.false (nat_lit 0) (nat_lit 1) (nat_lit 0) (nat_lit 1) Gram661ProofSharing.c379)

noncomputable def Gram661ProofSharing.c381 := (nat_lit 309485009821345068724781056000000000000)

noncomputable def Gram661ProofSharing.c382 := (@Inv.inv.{0} Complex Complex.instInv Gram661ProofSharing.c48)

noncomputable def Gram661ProofSharing.c383 := (BSN.zpow_one_sub_two_mul Gram661ProofSharing.c47 (nat_lit 2) (nat_lit 3) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram661ProofSharing.c384 := (Enclosure.Complex.inv_re_eq_mul Gram661ProofSharing.c48)

noncomputable def Gram661ProofSharing.c385 := (@Enclosure.Complex.IsNear.re_isNear Gram661ProofSharing.c48 Bool.true (nat_lit 77504530773203) (nat_lit 400000000) (nat_lit 0) (nat_lit 1) Bool.true (nat_lit 131313232456518478399) (nat_lit 1000000000000) (nat_lit 0) (nat_lit 1) Zeta.Certificates.Gram.gp7_cert._proof_2)

noncomputable def Gram661ProofSharing.c386 := (nat_lit 17243202561631472780816478648733285853201)

noncomputable def Gram661ProofSharing.c387 := (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) (Gram661ProofSharing.c48 : ℂ).re (Gram661ProofSharing.c48 : ℂ).re)

noncomputable def Gram661ProofSharing.c388 := (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) (Gram661ProofSharing.c48 : ℂ).im (Gram661ProofSharing.c48 : ℂ).im)

noncomputable def Gram661ProofSharing.c389 := (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd) Gram661ProofSharing.c387 Gram661ProofSharing.c388)

noncomputable def Gram661ProofSharing.c390 := (Enclosure.Complex.normSq_eq_mul_add_mul Gram661ProofSharing.c48)

noncomputable def Gram661ProofSharing.c391 := (nat_lit 17243165018179657940998872255738229603201)

noncomputable def Gram661ProofSharing.c392 := (nat_lit 2758912409861035644930636583797325736512160000000000000000)

noncomputable def Gram661ProofSharing.c393 := (@Enclosure.Real.IsNear.mulLit_tt (Gram661ProofSharing.c48 : ℂ).re (Gram661ProofSharing.c48 : ℂ).re (nat_lit 77504530773203) (nat_lit 400000000) (nat_lit 0) (nat_lit 1) (nat_lit 77504530773203) (nat_lit 400000000) (nat_lit 0) (nat_lit 1) (nat_lit 6006952290374370817022879209) (nat_lit 160000000000000000) (nat_lit 0) (nat_lit 1) Gram661ProofSharing.c385 Gram661ProofSharing.c385 (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram661ProofSharing.c394 := (@Enclosure.Complex.IsNear.im_isNear Gram661ProofSharing.c48 Bool.true (nat_lit 77504530773203) (nat_lit 400000000) (nat_lit 0) (nat_lit 1) Bool.true (nat_lit 131313232456518478399) (nat_lit 1000000000000) (nat_lit 0) (nat_lit 1) Zeta.Certificates.Gram.gp7_cert._proof_2)

noncomputable def Gram661ProofSharing.c395 := (@Enclosure.Real.IsNear.mulLit_tt (Gram661ProofSharing.c48 : ℂ).im (Gram661ProofSharing.c48 : ℂ).im (nat_lit 131313232456518478399) (nat_lit 1000000000000) (nat_lit 0) (nat_lit 1) (nat_lit 131313232456518478399) (nat_lit 1000000000000) (nat_lit 0) (nat_lit 1) Gram661ProofSharing.c391 (nat_lit 1000000000000000000000000) (nat_lit 0) (nat_lit 1) Gram661ProofSharing.c394 Gram661ProofSharing.c394 (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram661ProofSharing.c396 := (@Enclosure.Real.IsNear.addLit_ff Gram661ProofSharing.c387 Gram661ProofSharing.c388 (nat_lit 6006952290374370817022879209) (nat_lit 160000000000000000) (nat_lit 0) (nat_lit 1) Gram661ProofSharing.c391 (nat_lit 1000000000000000000000000) (nat_lit 0) (nat_lit 1) Gram661ProofSharing.c392 Gram661ProofSharing.c386 (nat_lit 1000000000000000000000000) (nat_lit 0) (nat_lit 1) Gram661ProofSharing.c393 Gram661ProofSharing.c395 (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram661ProofSharing.c397 := (@Neg.neg.{0} Real Real.instNeg (Gram661ProofSharing.c48 : ℂ).im)

noncomputable def Gram661ProofSharing.c398 := (Enclosure.Complex.inv_im_eq_mul Gram661ProofSharing.c48)

noncomputable def Gram661ProofSharing.c399 := (@Enclosure.Real.IsNear.neg (Gram661ProofSharing.c48 : ℂ).im Bool.true (nat_lit 131313232456518478399) (nat_lit 1000000000000) (nat_lit 0) (nat_lit 1) Gram661ProofSharing.c394)

noncomputable def Gram661ProofSharing.c400 := (@Enclosure.Complex.IsNear.im_isNear Gram661ProofSharing.c329 Bool.true (nat_lit 1) (nat_lit 360) (nat_lit 0) (nat_lit 1) Bool.false (nat_lit 0) (nat_lit 1) (nat_lit 0) (nat_lit 1) Gram661ProofSharing.c379)

noncomputable def Gram661ProofSharing.c401 := (BSN.logSumC Gram661ProofSharing.c39 (nat_lit 0))

noncomputable def Gram661ProofSharing.c402 := (Enclosure.sfrac Bool.false (nat_lit 98304000000000000000000000) Gram661ProofSharing.c106)

noncomputable def Gram661ProofSharing.c403 := (@Monoid.toNPow.{0} Real Real.instMonoid)

noncomputable def Gram661ProofSharing.c404 := (@NPow.toPow.{0} Real Gram661ProofSharing.c403)

noncomputable def Gram661ProofSharing.c405 := (@instHPow.{0, 0} Real Nat Gram661ProofSharing.c404)

noncomputable def Gram661ProofSharing.c406 := (@HPow.hPow.{0, 0, 0} Real Nat Real Gram661ProofSharing.c405 Gram661ProofSharing.c7 (nat_lit 4))

noncomputable def Gram661ProofSharing.c407 := (@Inv.inv.{0} Real Real.instInv Gram661ProofSharing.c406)

noncomputable def Gram661ProofSharing.c408 := (nat_lit 611446774371975769155682509262542103857872115376664175900625)

noncomputable def Gram661ProofSharing.c409 := (nat_lit 392318858461667547739736838950479151006397215279002157056)

noncomputable def Gram661ProofSharing.c410 := (nat_lit 19652562622312316682495810535216024035134795670488584765154486969712234385047)

noncomputable def Gram661ProofSharing.c411 := (nat_lit 9903520314283042199192993792000000000000000000000000000000000000000000000000000000000000)

noncomputable def Gram661ProofSharing.c412 := (@HPow.hPow.{0, 0, 0} Real Nat Real Gram661ProofSharing.c405 Gram661ProofSharing.c7 (nat_lit 3))

noncomputable def Gram661ProofSharing.c413 := (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) Gram661ProofSharing.c412 Gram661ProofSharing.c7)

noncomputable def Gram661ProofSharing.c414 := (BSN.pow_succ_r Gram661ProofSharing.c7 (nat_lit 3) (nat_lit 4) (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram661ProofSharing.c415 := (nat_lit 691463075802508163054686763366652189853178875)

noncomputable def Gram661ProofSharing.c416 := (nat_lit 2787593149816327892691964784081045188247552)

noncomputable def Gram661ProofSharing.c417 := (nat_lit 2184744797947834540264818678394244808492865883128339)

noncomputable def Gram661ProofSharing.c418 := (nat_lit 9223372036854775808000000000000000000000000000000000000000000000)

noncomputable def Gram661ProofSharing.c419 := (@HPow.hPow.{0, 0, 0} Real Nat Real Gram661ProofSharing.c405 Gram661ProofSharing.c7 (nat_lit 2))

noncomputable def Gram661ProofSharing.c420 := (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) Gram661ProofSharing.c419 Gram661ProofSharing.c7)

noncomputable def Gram661ProofSharing.c421 := (BSN.pow_succ_r Gram661ProofSharing.c7 (nat_lit 2) (nat_lit 3) (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram661ProofSharing.c422 := (nat_lit 1073741824000000000000000000000000000000)

noncomputable def Gram661ProofSharing.c423 := (@HPow.hPow.{0, 0, 0} Real Nat Real Gram661ProofSharing.c405 Gram661ProofSharing.c7 (nat_lit 1))

noncomputable def Gram661ProofSharing.c424 := (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) Gram661ProofSharing.c423 Gram661ProofSharing.c7)

noncomputable def Gram661ProofSharing.c425 := (BSN.pow_succ_r Gram661ProofSharing.c7 (nat_lit 1) (nat_lit 2) (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram661ProofSharing.c426 := (BSN.pow_one_r Gram661ProofSharing.c7)

noncomputable def Gram661ProofSharing.c427 := (@Enclosure.Real.IsNear.of_eq Gram661ProofSharing.c7 Gram661ProofSharing.c10 Bool.false (nat_lit 884279719003555) (nat_lit 140737488355328) (nat_lit 1) (nat_lit 500000000000000) BSN.two_pi_eq Gram661ProofSharing.c13)

noncomputable def Gram661ProofSharing.c428 := (@Enclosure.Real.IsNear.of_eq Gram661ProofSharing.c423 Gram661ProofSharing.c7 Bool.false (nat_lit 884279719003555) (nat_lit 140737488355328) (nat_lit 1) (nat_lit 500000000000000) Gram661ProofSharing.c426 Gram661ProofSharing.c427)

noncomputable def Gram661ProofSharing.c429 := (@Enclosure.Real.IsNear.mulLit_ff Gram661ProofSharing.c423 Gram661ProofSharing.c7 (nat_lit 884279719003555) (nat_lit 140737488355328) (nat_lit 1) (nat_lit 500000000000000) (nat_lit 884279719003555) (nat_lit 140737488355328) (nat_lit 1) (nat_lit 500000000000000) (nat_lit 781950621441006189802102638025) (nat_lit 19807040628566084398385987584) (nat_lit 26986075409044041160201671) Gram661ProofSharing.c422 Gram661ProofSharing.c428 Gram661ProofSharing.c427 (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram661ProofSharing.c430 := (@Enclosure.Real.IsNear.of_eq Gram661ProofSharing.c419 Gram661ProofSharing.c424 Bool.false (nat_lit 781950621441006189802102638025) (nat_lit 19807040628566084398385987584) (nat_lit 26986075409044041160201671) Gram661ProofSharing.c422 Gram661ProofSharing.c425 Gram661ProofSharing.c429)

noncomputable def Gram661ProofSharing.c431 := (@Enclosure.Real.IsNear.mulLit_ff Gram661ProofSharing.c419 Gram661ProofSharing.c7 (nat_lit 781950621441006189802102638025) (nat_lit 19807040628566084398385987584) (nat_lit 26986075409044041160201671) Gram661ProofSharing.c422 (nat_lit 884279719003555) (nat_lit 140737488355328) (nat_lit 1) (nat_lit 500000000000000) Gram661ProofSharing.c415 Gram661ProofSharing.c416 Gram661ProofSharing.c417 Gram661ProofSharing.c418 Gram661ProofSharing.c430 Gram661ProofSharing.c427 (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram661ProofSharing.c432 := (@Enclosure.Real.IsNear.of_eq Gram661ProofSharing.c412 Gram661ProofSharing.c420 Bool.false Gram661ProofSharing.c415 Gram661ProofSharing.c416 Gram661ProofSharing.c417 Gram661ProofSharing.c418 Gram661ProofSharing.c421 Gram661ProofSharing.c431)

noncomputable def Gram661ProofSharing.c433 := (@Enclosure.Real.IsNear.mulLit_ff Gram661ProofSharing.c412 Gram661ProofSharing.c7 Gram661ProofSharing.c415 Gram661ProofSharing.c416 Gram661ProofSharing.c417 Gram661ProofSharing.c418 (nat_lit 884279719003555) (nat_lit 140737488355328) (nat_lit 1) (nat_lit 500000000000000) Gram661ProofSharing.c408 Gram661ProofSharing.c409 Gram661ProofSharing.c410 Gram661ProofSharing.c411 Gram661ProofSharing.c432 Gram661ProofSharing.c427 (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram661ProofSharing.c434 := (@Enclosure.Real.IsNear.of_eq Gram661ProofSharing.c406 Gram661ProofSharing.c413 Bool.false Gram661ProofSharing.c408 Gram661ProofSharing.c409 Gram661ProofSharing.c410 Gram661ProofSharing.c411 Gram661ProofSharing.c414 Gram661ProofSharing.c433)

noncomputable def Gram661ProofSharing.c435 := (@Enclosure.Real.IsNear.inv_image Gram661ProofSharing.c406 Gram661ProofSharing.c408 Gram661ProofSharing.c409 Gram661ProofSharing.c410 Gram661ProofSharing.c411 (nat_lit 5511507) (nat_lit 5511508) (nat_lit 8589934592) Gram661ProofSharing.c434 (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram661ProofSharing.c436 := (@Enclosure.Real.IsNear.recentre' Gram661ProofSharing.c407 Bool.false (nat_lit 11023015) (nat_lit 17179869184) (nat_lit 1) (nat_lit 17179869184) (nat_lit 11023015) (nat_lit 17179869184) (nat_lit 1) (nat_lit 17179869184) Gram661ProofSharing.c435 (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram661ProofSharing.c437 := (nat_lit 23224357924529686803982156250793039965983)

noncomputable def Gram661ProofSharing.c438 := (nat_lit 891316828285473797927369441280000000000000000)

noncomputable def Gram661ProofSharing.c439 := (nat_lit 961403688695763298440525894269225277570517)

noncomputable def Gram661ProofSharing.c440 := (nat_lit 6127803194462632360750664908800000000000000000000)

noncomputable def Gram661ProofSharing.c441 := (nat_lit 1708645511023987856946718085944336)

noncomputable def Gram661ProofSharing.c442 := (riemannSiegelThetaApproximant (nat_lit 2) (nat_lit 0) Gram661ProofSharing.c107)

noncomputable def Gram661ProofSharing.c443 := (nat_lit 1850902081467436259923812932724556250793039965983)

noncomputable def Gram661ProofSharing.c444 := (nat_lit 961399638217851758640535438079720560770517)

noncomputable def Gram661ProofSharing.c445 := (Complex.Stirling.logGammaStirling (nat_lit 2) Gram661ProofSharing.c112)

noncomputable def Gram661ProofSharing.c446 := (@HDiv.hDiv.{0, 0, 0} Real Real Real Gram661ProofSharing.c15 Gram661ProofSharing.c107 Gram661ProofSharing.c6)

noncomputable def Gram661ProofSharing.c447 := (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) Gram661ProofSharing.c446 (Real.log Real.pi))

noncomputable def Gram661ProofSharing.c448 := (nat_lit 2369508725091515791157943762682374209193039965983)

noncomputable def Gram661ProofSharing.c449 := (nat_lit 236216168318341900533667726079720560770517)

noncomputable def Gram661ProofSharing.c450 := (nat_lit 14244010214791688563783919997733551701710003)

noncomputable def Gram661ProofSharing.c451 := (nat_lit 17826336565709475958547388825600000000000)

noncomputable def Gram661ProofSharing.c452 := (nat_lit 29546627555408299578729080607092481351461)

noncomputable def Gram661ProofSharing.c453 := (nat_lit 382987699653914522546916556800000000000000000000)

noncomputable def Gram661ProofSharing.c454 := (@HSub.hSub.{0, 0, 0} Complex Complex Complex (@instHSub.{0} Complex Complex.instSub) Gram661ProofSharing.c112 Gram661ProofSharing.c233)

noncomputable def Gram661ProofSharing.c455 := (Complex.log Gram661ProofSharing.c112)

noncomputable def Gram661ProofSharing.c456 := (@HMul.hMul.{0, 0, 0} Complex Complex Complex (@instHMul.{0} Complex Complex.instMul) Gram661ProofSharing.c454 Gram661ProofSharing.c455)

noncomputable def Gram661ProofSharing.c457 := (@HSub.hSub.{0, 0, 0} Complex Complex Complex (@instHSub.{0} Complex Complex.instSub) Gram661ProofSharing.c456 Gram661ProofSharing.c112)

noncomputable def Gram661ProofSharing.c458 := (@HAdd.hAdd.{0, 0, 0} Complex Complex Complex (@instHAdd.{0} Complex Complex.instAdd) Gram661ProofSharing.c457 Gram661ProofSharing.c238)

noncomputable def Gram661ProofSharing.c459 := (nat_lit 1437523755602306288349364650289997)

noncomputable def Gram661ProofSharing.c460 := (nat_lit 146132852752124082093004481675606960034017)

noncomputable def Gram661ProofSharing.c461 := (nat_lit 8382896201118406443172499747087)

noncomputable def Gram661ProofSharing.c462 := (BSN.w_sub_half_zero_mk Gram661ProofSharing.c107 Bool.false (nat_lit 101655983) (nat_lit 100000) Gram661ProofSharing.c121 (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram661ProofSharing.c463 := (@Enclosure.Complex.IsNear.mk Gram661ProofSharing.c248 Gram661ProofSharing.c123 Bool.true (nat_lit 100000) (nat_lit 400000) (nat_lit 0) (nat_lit 1) Bool.false (nat_lit 203311966) (nat_lit 400000) (nat_lit 0) (nat_lit 1) Gram661ProofSharing.c249 Gram661ProofSharing.c124)

noncomputable def Gram661ProofSharing.c464 := (@Enclosure.Complex.IsNear.of_eq Gram661ProofSharing.c454 { re := Enclosure.sfrac Bool.true (nat_lit 100000) (nat_lit 400000), im := Enclosure.sfrac Bool.false (nat_lit 203311966) (nat_lit 400000) } Bool.true (nat_lit 100000) (nat_lit 400000) (nat_lit 0) (nat_lit 1) Bool.false (nat_lit 203311966) (nat_lit 400000) (nat_lit 0) (nat_lit 1) Gram661ProofSharing.c462 Gram661ProofSharing.c463)

noncomputable def Gram661ProofSharing.c465 := (@Enclosure.Complex.IsNear.re_isNear Gram661ProofSharing.c454 Bool.true (nat_lit 100000) (nat_lit 400000) (nat_lit 0) (nat_lit 1) Bool.false (nat_lit 203311966) (nat_lit 400000) (nat_lit 0) (nat_lit 1) Gram661ProofSharing.c464)

noncomputable def Gram661ProofSharing.c466 := (Complex.log { re := Enclosure.sfrac Bool.false (nat_lit 100000) (nat_lit 400000), im := Enclosure.sfrac Bool.false (nat_lit 203311966) (nat_lit 400000) })

noncomputable def Gram661ProofSharing.c467 := (@congrArg.{1, 1} Complex Complex Gram661ProofSharing.c112 { re := Enclosure.sfrac Bool.false (nat_lit 100000) (nat_lit 400000), im := Enclosure.sfrac Bool.false (nat_lit 203311966) (nat_lit 400000) } Complex.log Gram661ProofSharing.c122)

noncomputable def Gram661ProofSharing.c468 := (Enclosure.sfrac Bool.false (nat_lit 41335765518785156) (nat_lit 160000000000))

noncomputable def Gram661ProofSharing.c469 := (Real.log Gram661ProofSharing.c468)

noncomputable def Gram661ProofSharing.c470 := (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) Gram661ProofSharing.c255 Gram661ProofSharing.c469)

noncomputable def Gram661ProofSharing.c471 := (Enclosure.clog_re_eq (nat_lit 100000) (nat_lit 203311966) (nat_lit 400000) (nat_lit 41335765518785156) (nat_lit 160000000000) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram661ProofSharing.c472 := (@Nat.cast.{0} Real Real.instNatCast (nat_lit 41335765518785156))

noncomputable def Gram661ProofSharing.c473 := (@HDiv.hDiv.{0, 0, 0} Real Real Real Gram661ProofSharing.c15 Gram661ProofSharing.c472 Gram661ProofSharing.c262)

noncomputable def Gram661ProofSharing.c474 := (Real.log Gram661ProofSharing.c473)

noncomputable def Gram661ProofSharing.c475 := (nat_lit 10691965424788208483299434628431974160814196160984079241357835077727380888885359551067349851322425486896595794649590193669169811065073256229302102060474322937678002508485104800201995220309402704615689859460158040778264620722452425111776091245266358029872101049815127849295151674490930418054944701790018463181236966725781986077426278492097688371200)

noncomputable def Gram661ProofSharing.c476 := (nat_lit 407143118980098078292880034505472340986591627102522597020884916644478743489723155329389832303464513337405508361773159747767659566192580729966157084491296887882044071157685715971155034538478719340241645195287371537373738110270578676283550185146160557673159911271583502404996562801930931087764140162844086409569757636501979224370183125497880248320)

noncomputable def Gram661ProofSharing.c477 := (nat_lit 98498159511245828821122229988952113884593269082162511119222109813573962979469496203592144258168304996618359470204347515257925105094578965710254126637508729579008541129290519832911588479032937569467737930065718882561122805238725325345710025469124003938962164396022891827626269123779980440066999184696946874916164607682304492004651827200)

noncomputable def Gram661ProofSharing.c478 := (BSN.artanhP (nat_lit 20364245518785156))

noncomputable def Gram661ProofSharing.c479 := (BSN.artanhQ (nat_lit 62307285518785156))

noncomputable def Gram661ProofSharing.c480 := (@BSN.binarySplit_of_base10 Gram661ProofSharing.c478 Gram661ProofSharing.c479 (nat_lit 0) (nat_lit 10) Gram661ProofSharing.c476 Gram661ProofSharing.c475 Gram661ProofSharing.c477 (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram661ProofSharing.c481 := (BSN.log_dyadic_bound (nat_lit 20364245518785156) (nat_lit 62307285518785156) (nat_lit 11) (nat_lit 10) Gram661ProofSharing.c475 (nat_lit 17179869184) (nat_lit 6600000000) Gram661ProofSharing.c476 Gram661ProofSharing.c477 (nat_lit 11657619993) (nat_lit 82671531037570312) (nat_lit 41943040000000000) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) Gram661ProofSharing.c480 (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram661ProofSharing.c482 := (BSN.log_rat_reduce_isNear (nat_lit 41335765518785156) (nat_lit 160000000000) (nat_lit 17) (nat_lit 82671531037570312) (nat_lit 41943040000000000) (nat_lit 11657619993) (nat_lit 17179869184) (nat_lit 24973259072661432) (nat_lit 36028797018963968) (nat_lit 6600000000) (nat_lit 1000000000000000) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) Gram661ProofSharing.c481 BSN.log2_near_15 (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram661ProofSharing.c483 := (@Enclosure.Real.IsNear.recentre' Gram661ProofSharing.c474 Bool.false (nat_lit 7713644531881910545699307520) (nat_lit 618970019642690137449562112) (nat_lit 1000112200000000) (nat_lit 6600000000000000000000000) (nat_lit 56124150664850535) (nat_lit 4503599627370496) (nat_lit 5000561) (nat_lit 33000000000000000) Gram661ProofSharing.c482 (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram661ProofSharing.c484 := (BSN.isNear_log_sfrac (nat_lit 41335765518785156) (nat_lit 160000000000) (nat_lit 56124150664850535) (nat_lit 4503599627370496) (nat_lit 5000561) (nat_lit 33000000000000000) Bool.false Gram661ProofSharing.c483)

noncomputable def Gram661ProofSharing.c485 := (@Enclosure.Real.IsNear.mulLit_ff Gram661ProofSharing.c255 Gram661ProofSharing.c469 (nat_lit 1) (nat_lit 2) (nat_lit 0) (nat_lit 1) (nat_lit 56124150664850535) (nat_lit 4503599627370496) (nat_lit 5000561) (nat_lit 33000000000000000) (nat_lit 56124150664850535) (nat_lit 9007199254740992) (nat_lit 5000561) (nat_lit 66000000000000000) Gram661ProofSharing.c260 Gram661ProofSharing.c484 (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram661ProofSharing.c486 := (@Enclosure.Real.IsNear.of_eq (Gram661ProofSharing.c466 : ℂ).re Gram661ProofSharing.c470 Bool.false (nat_lit 56124150664850535) (nat_lit 9007199254740992) (nat_lit 5000561) (nat_lit 66000000000000000) Gram661ProofSharing.c471 Gram661ProofSharing.c485)

noncomputable def Gram661ProofSharing.c487 := (@Nat.cast.{0} Real Real.instNatCast (nat_lit 203311966))

noncomputable def Gram661ProofSharing.c488 := (@HDiv.hDiv.{0, 0, 0} Real Real Real Gram661ProofSharing.c15 Gram661ProofSharing.c487 Gram661ProofSharing.c278)

noncomputable def Gram661ProofSharing.c489 := (Real.arctan Gram661ProofSharing.c488)

noncomputable def Gram661ProofSharing.c490 := (Enclosure.clog_im_eq (nat_lit 100000) (nat_lit 203311966) (nat_lit 400000) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram661ProofSharing.c491 := (@HDiv.hDiv.{0, 0, 0} Real Real Real Gram661ProofSharing.c15 Gram661ProofSharing.c278 Gram661ProofSharing.c487)

noncomputable def Gram661ProofSharing.c492 := (Real.arctan Gram661ProofSharing.c491)

noncomputable def Gram661ProofSharing.c493 := (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) Gram661ProofSharing.c282 Gram661ProofSharing.c492)

noncomputable def Gram661ProofSharing.c494 := (BSN.arctan_recip (nat_lit 203311966) (nat_lit 100000) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram661ProofSharing.c495 := (@BSN.binarySplit_of_le (BSN.arctanEvenP (nat_lit 100000)) (BSN.arctanEvenQ (nat_lit 203311966)) (nat_lit 0) (nat_lit 0) (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram661ProofSharing.c496 := (@BSN.binarySplit_of_le (BSN.arctanOddP (nat_lit 100000)) (BSN.arctanOddQ (nat_lit 203311966)) (nat_lit 0) (nat_lit 0) (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram661ProofSharing.c497 := (BSN.arctan_dyadic_bound_f (nat_lit 100000) (nat_lit 203311966) (nat_lit 1) (nat_lit 0) (nat_lit 17179869184) (nat_lit 6600000000) (nat_lit 0) (nat_lit 1) (nat_lit 1) (nat_lit 0) (nat_lit 1) (nat_lit 1) (nat_lit 8450003) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) Gram661ProofSharing.c495 Gram661ProofSharing.c496 (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram661ProofSharing.c498 := (@Enclosure.Real.IsNear.subLit_ff_p Gram661ProofSharing.c282 Gram661ProofSharing.c492 (nat_lit 884279719003555) (nat_lit 562949953421312) (nat_lit 1) (nat_lit 2000000000000000) (nat_lit 8450003) (nat_lit 17179869184) (nat_lit 1) (nat_lit 6600000000) (nat_lit 15187052965750093784285184) (nat_lit 884002829305251) (nat_lit 562949953421312) (nat_lit 10000033) (nat_lit 66000000000000000) Gram661ProofSharing.c287 Gram661ProofSharing.c497 (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram661ProofSharing.c499 := (@Enclosure.Real.IsNear.of_eq Gram661ProofSharing.c489 Gram661ProofSharing.c493 Bool.false (nat_lit 884002829305251) (nat_lit 562949953421312) (nat_lit 10000033) (nat_lit 66000000000000000) Gram661ProofSharing.c494 Gram661ProofSharing.c498)

noncomputable def Gram661ProofSharing.c500 := (@Enclosure.Real.IsNear.of_eq (Gram661ProofSharing.c466 : ℂ).im Gram661ProofSharing.c489 Bool.false (nat_lit 884002829305251) (nat_lit 562949953421312) (nat_lit 10000033) (nat_lit 66000000000000000) Gram661ProofSharing.c490 Gram661ProofSharing.c499)

noncomputable def Gram661ProofSharing.c501 := (@Enclosure.Complex.IsNear.of_parts Gram661ProofSharing.c466 Bool.false (nat_lit 56124150664850535) (nat_lit 9007199254740992) (nat_lit 5000561) (nat_lit 66000000000000000) Bool.false (nat_lit 884002829305251) (nat_lit 562949953421312) (nat_lit 10000033) (nat_lit 66000000000000000) Gram661ProofSharing.c486 Gram661ProofSharing.c500)

noncomputable def Gram661ProofSharing.c502 := (@Enclosure.Complex.IsNear.of_eq Gram661ProofSharing.c455 Gram661ProofSharing.c466 Bool.false (nat_lit 56124150664850535) (nat_lit 9007199254740992) (nat_lit 5000561) (nat_lit 66000000000000000) Bool.false (nat_lit 884002829305251) (nat_lit 562949953421312) (nat_lit 10000033) (nat_lit 66000000000000000) Gram661ProofSharing.c467 Gram661ProofSharing.c501)

noncomputable def Gram661ProofSharing.c503 := (@Enclosure.Complex.IsNear.re_isNear Gram661ProofSharing.c455 Bool.false (nat_lit 56124150664850535) (nat_lit 9007199254740992) (nat_lit 5000561) (nat_lit 66000000000000000) Bool.false (nat_lit 884002829305251) (nat_lit 562949953421312) (nat_lit 10000033) (nat_lit 66000000000000000) Gram661ProofSharing.c502)

noncomputable def Gram661ProofSharing.c504 := (@Enclosure.Complex.IsNear.im_isNear Gram661ProofSharing.c454 Bool.true (nat_lit 100000) (nat_lit 400000) (nat_lit 0) (nat_lit 1) Bool.false (nat_lit 203311966) (nat_lit 400000) (nat_lit 0) (nat_lit 1) Gram661ProofSharing.c464)

noncomputable def Gram661ProofSharing.c505 := (@Enclosure.Complex.IsNear.im_isNear Gram661ProofSharing.c455 Bool.false (nat_lit 56124150664850535) (nat_lit 9007199254740992) (nat_lit 5000561) (nat_lit 66000000000000000) Bool.false (nat_lit 884002829305251) (nat_lit 562949953421312) (nat_lit 10000033) (nat_lit 66000000000000000) Gram661ProofSharing.c502)

noncomputable def Gram661ProofSharing.c506 := (@HPow.hPow.{0, 0, 0} Complex Int Complex Gram661ProofSharing.c242 Gram661ProofSharing.c112 Gram661ProofSharing.c332)

noncomputable def Gram661ProofSharing.c507 := (@HMul.hMul.{0, 0, 0} Complex Complex Complex (@instHMul.{0} Complex Complex.instMul) Gram661ProofSharing.c329 Gram661ProofSharing.c506)

noncomputable def Gram661ProofSharing.c508 := (nat_lit 18854721814909097298674006960034017)

noncomputable def Gram661ProofSharing.c509 := (@HPow.hPow.{0, 0, 0} Complex Int Complex Gram661ProofSharing.c242 Gram661ProofSharing.c112 Gram661ProofSharing.c346)

noncomputable def Gram661ProofSharing.c510 := (@HMul.hMul.{0, 0, 0} Complex Complex Complex (@instHMul.{0} Complex Complex.instMul) Gram661ProofSharing.c343 Gram661ProofSharing.c509)

noncomputable def Gram661ProofSharing.c511 := (@Inv.inv.{0} Complex Complex.instInv Gram661ProofSharing.c115)

noncomputable def Gram661ProofSharing.c512 := (BSN.zpow_one_sub_two_mul Gram661ProofSharing.c112 (nat_lit 1) (nat_lit 1) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram661ProofSharing.c513 := (Enclosure.Complex.inv_re_eq_mul Gram661ProofSharing.c115)

noncomputable def Gram661ProofSharing.c514 := (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) (Gram661ProofSharing.c115 : ℂ).re (Gram661ProofSharing.c115 : ℂ).re)

noncomputable def Gram661ProofSharing.c515 := (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) (Gram661ProofSharing.c115 : ℂ).im (Gram661ProofSharing.c115 : ℂ).im)

noncomputable def Gram661ProofSharing.c516 := (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd) Gram661ProofSharing.c514 Gram661ProofSharing.c515)

noncomputable def Gram661ProofSharing.c517 := (Enclosure.Complex.normSq_eq_mul_add_mul Gram661ProofSharing.c115)

noncomputable def Gram661ProofSharing.c518 := (@Enclosure.Real.IsNear.mulLit_ff (Gram661ProofSharing.c115 : ℂ).re (Gram661ProofSharing.c115 : ℂ).re (nat_lit 100000) (nat_lit 400000) (nat_lit 0) (nat_lit 1) (nat_lit 100000) (nat_lit 400000) (nat_lit 0) (nat_lit 1) (nat_lit 1) (nat_lit 16) (nat_lit 0) (nat_lit 1) Gram661ProofSharing.c128 Gram661ProofSharing.c128 (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram661ProofSharing.c519 := (@Enclosure.Real.IsNear.mulLit_ff (Gram661ProofSharing.c115 : ℂ).im (Gram661ProofSharing.c115 : ℂ).im (nat_lit 203311966) (nat_lit 400000) (nat_lit 0) (nat_lit 1) (nat_lit 203311966) (nat_lit 400000) (nat_lit 0) (nat_lit 1) (nat_lit 10333938879696289) (nat_lit 40000000000) (nat_lit 0) (nat_lit 1) Gram661ProofSharing.c131 Gram661ProofSharing.c131 (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram661ProofSharing.c520 := (@Enclosure.Real.IsNear.addLit_ff Gram661ProofSharing.c514 Gram661ProofSharing.c515 (nat_lit 1) (nat_lit 16) (nat_lit 0) (nat_lit 1) (nat_lit 10333938879696289) (nat_lit 40000000000) (nat_lit 0) (nat_lit 1) (nat_lit 165343062075140624) (nat_lit 10333941379696289) (nat_lit 40000000000) (nat_lit 0) (nat_lit 1) Gram661ProofSharing.c518 Gram661ProofSharing.c519 (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram661ProofSharing.c521 := (@Neg.neg.{0} Real Real.instNeg (Gram661ProofSharing.c115 : ℂ).im)

noncomputable def Gram661ProofSharing.c522 := (Enclosure.Complex.inv_im_eq_mul Gram661ProofSharing.c115)

noncomputable def Gram661ProofSharing.c523 := (@Enclosure.Real.IsNear.neg (Gram661ProofSharing.c115 : ℂ).im Bool.false (nat_lit 203311966) (nat_lit 400000) (nat_lit 0) (nat_lit 1) Gram661ProofSharing.c131)

noncomputable def Gram661ProofSharing.c524 := (nat_lit 49517601571415210995964968960000000000)

noncomputable def Gram661ProofSharing.c525 := (nat_lit 2475880078570760549798248448000000000000000)

noncomputable def Gram661ProofSharing.c526 := (@Inv.inv.{0} Complex Complex.instInv Gram661ProofSharing.c113)

noncomputable def Gram661ProofSharing.c527 := (BSN.zpow_one_sub_two_mul Gram661ProofSharing.c112 (nat_lit 2) (nat_lit 3) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram661ProofSharing.c528 := (Enclosure.Complex.inv_re_eq_mul Gram661ProofSharing.c113)

noncomputable def Gram661ProofSharing.c529 := (@Enclosure.Complex.IsNear.re_isNear Gram661ProofSharing.c113 Bool.true (nat_lit 31001814139088867) (nat_lit 160000000000) (nat_lit 0) (nat_lit 1) Bool.true (nat_lit 1050505952657572499747087) (nat_lit 8000000000000000) (nat_lit 0) (nat_lit 1) Zeta.Certificates.Gram.gp7_cert._proof_6)

noncomputable def Gram661ProofSharing.c530 := (nat_lit 1103565159350193740670037756719589091901464985569)

noncomputable def Gram661ProofSharing.c531 := (nat_lit 64000000000000000000000000000000)

noncomputable def Gram661ProofSharing.c532 := (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) (Gram661ProofSharing.c113 : ℂ).re (Gram661ProofSharing.c113 : ℂ).re)

noncomputable def Gram661ProofSharing.c533 := (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) (Gram661ProofSharing.c113 : ℂ).im (Gram661ProofSharing.c113 : ℂ).im)

noncomputable def Gram661ProofSharing.c534 := (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd) Gram661ProofSharing.c532 Gram661ProofSharing.c533)

noncomputable def Gram661ProofSharing.c535 := (Enclosure.Complex.normSq_eq_mul_add_mul Gram661ProofSharing.c113)

noncomputable def Gram661ProofSharing.c536 := (nat_lit 961112479914610387755188923343689)

noncomputable def Gram661ProofSharing.c537 := (nat_lit 1103562756568993954144068368747280732678964985569)

noncomputable def Gram661ProofSharing.c538 := (nat_lit 28251268079364959761152966572021480752677503630566400000000000000000000)

noncomputable def Gram661ProofSharing.c539 := (@Enclosure.Real.IsNear.mulLit_tt (Gram661ProofSharing.c113 : ℂ).re (Gram661ProofSharing.c113 : ℂ).re (nat_lit 31001814139088867) (nat_lit 160000000000) (nat_lit 0) (nat_lit 1) (nat_lit 31001814139088867) (nat_lit 160000000000) (nat_lit 0) (nat_lit 1) Gram661ProofSharing.c536 (nat_lit 25600000000000000000000) (nat_lit 0) (nat_lit 1) Gram661ProofSharing.c529 Gram661ProofSharing.c529 (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram661ProofSharing.c540 := (@Enclosure.Complex.IsNear.im_isNear Gram661ProofSharing.c113 Bool.true (nat_lit 31001814139088867) (nat_lit 160000000000) (nat_lit 0) (nat_lit 1) Bool.true (nat_lit 1050505952657572499747087) (nat_lit 8000000000000000) (nat_lit 0) (nat_lit 1) Zeta.Certificates.Gram.gp7_cert._proof_6)

noncomputable def Gram661ProofSharing.c541 := (@Enclosure.Real.IsNear.mulLit_tt (Gram661ProofSharing.c113 : ℂ).im (Gram661ProofSharing.c113 : ℂ).im (nat_lit 1050505952657572499747087) (nat_lit 8000000000000000) (nat_lit 0) (nat_lit 1) (nat_lit 1050505952657572499747087) (nat_lit 8000000000000000) (nat_lit 0) (nat_lit 1) Gram661ProofSharing.c537 Gram661ProofSharing.c531 (nat_lit 0) (nat_lit 1) Gram661ProofSharing.c540 Gram661ProofSharing.c540 (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram661ProofSharing.c542 := (@Enclosure.Real.IsNear.addLit_ff Gram661ProofSharing.c532 Gram661ProofSharing.c533 Gram661ProofSharing.c536 (nat_lit 25600000000000000000000) (nat_lit 0) (nat_lit 1) Gram661ProofSharing.c537 Gram661ProofSharing.c531 (nat_lit 0) (nat_lit 1) Gram661ProofSharing.c538 Gram661ProofSharing.c530 Gram661ProofSharing.c531 (nat_lit 0) (nat_lit 1) Gram661ProofSharing.c539 Gram661ProofSharing.c541 (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram661ProofSharing.c543 := (@Neg.neg.{0} Real Real.instNeg (Gram661ProofSharing.c113 : ℂ).im)

noncomputable def Gram661ProofSharing.c544 := (Enclosure.Complex.inv_im_eq_mul Gram661ProofSharing.c113)

noncomputable def Gram661ProofSharing.c545 := (@Enclosure.Real.IsNear.neg (Gram661ProofSharing.c113 : ℂ).im Bool.true (nat_lit 1050505952657572499747087) (nat_lit 8000000000000000) (nat_lit 0) (nat_lit 1) Gram661ProofSharing.c540)

noncomputable def Gram661ProofSharing.c546 := (BSN.logSumC Gram661ProofSharing.c107 (nat_lit 0))

noncomputable def Gram661ProofSharing.c547 := (Enclosure.sfrac Bool.false (nat_lit 98304000000000000000000000) Gram661ProofSharing.c144)


