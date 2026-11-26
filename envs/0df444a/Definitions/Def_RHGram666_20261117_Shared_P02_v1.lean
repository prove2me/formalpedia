-- Prove2me | Definitions.Def_RHGram666_20261117_Shared_P02_v1
-- name    : RHGram666_20261117_Shared_P02_v1
-- status  : Definition
-- author  : @bueno_ricardo
-- created : 2026-11-17T23:13:35.198778+00:00
-- url     : https://prove2.me/theorems/ae5e28f6-ecd3-48d4-b5f4-3ebecf1a0128
-- title:
--   Gram 666 ordinary shared terms, part 2
-- statement:
--   Exact shared expressions and complete ordinary auxiliary proofs for the endpoint certificate of Gram point 666. No additional axioms or custom proof generators. Imports the already published analytic and numerical support modules.
-- source:
--   Salvatore Mercuri and Bhavik Mehta, smmercuri/zeta commit 3dab6480a82f1bfc5de0a59550e279cf50490033; Apache-2.0. Ordinary proof export and exact sharing by Desenvolvimento RH. Full expanded strict AXLE and cumulative prefixes: e90cdbe8-beda-4ed3-aeb1-1e4032a8f245.

import Definitions.Def_RHGram666_20261117_Shared_P01_v1
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
noncomputable def Gram666ProofSharing.c225 := (@HDiv.hDiv.{0, 0, 0} Real Real Real Gram666ProofSharing.c15 Gram666ProofSharing.c39 Gram666ProofSharing.c6)

noncomputable def Gram666ProofSharing.c226 := (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) Gram666ProofSharing.c225 (Real.log Real.pi))

noncomputable def Gram666ProofSharing.c227 := (nat_lit 265184286355583430928672692389359026358859053)

noncomputable def Gram666ProofSharing.c228 := (nat_lit 990208109942389019228119837982380692271)

noncomputable def Gram666ProofSharing.c229 := (nat_lit 143304621405278782210967479927704440924353)

noncomputable def Gram666ProofSharing.c230 := (nat_lit 178263365657094759585473888256000000000)

noncomputable def Gram666ProofSharing.c231 := (nat_lit 2229531241845278739597123760323821956699)

noncomputable def Gram666ProofSharing.c232 := (nat_lit 29594504064166122196807188480000000000000000000)

noncomputable def Gram666ProofSharing.c233 := (@HDiv.hDiv.{0, 0, 0} Complex Complex Complex Gram666ProofSharing.c28 Gram666ProofSharing.c30 Gram666ProofSharing.c42)

noncomputable def Gram666ProofSharing.c234 := (@HSub.hSub.{0, 0, 0} Complex Complex Complex (@instHSub.{0} Complex Complex.instSub) Gram666ProofSharing.c47 Gram666ProofSharing.c233)

noncomputable def Gram666ProofSharing.c235 := (Complex.log Gram666ProofSharing.c47)

noncomputable def Gram666ProofSharing.c236 := (@HMul.hMul.{0, 0, 0} Complex Complex Complex (@instHMul.{0} Complex Complex.instMul) Gram666ProofSharing.c234 Gram666ProofSharing.c235)

noncomputable def Gram666ProofSharing.c237 := (@HSub.hSub.{0, 0, 0} Complex Complex Complex (@instHSub.{0} Complex Complex.instSub) Gram666ProofSharing.c236 Gram666ProofSharing.c47)

noncomputable def Gram666ProofSharing.c238 := (@HMul.hMul.{0, 0, 0} Complex Complex Complex (@instHMul.{0} Complex Complex.instMul) Gram666ProofSharing.c233 ↑Gram666ProofSharing.c8)

noncomputable def Gram666ProofSharing.c239 := (@HAdd.hAdd.{0, 0, 0} Complex Complex Complex (@instHAdd.{0} Complex Complex.instAdd) Gram666ProofSharing.c237 Gram666ProofSharing.c238)

noncomputable def Gram666ProofSharing.c240 := (@DivInvMonoid.toZPow.{0} Complex Complex.instDivInvMonoid)

noncomputable def Gram666ProofSharing.c241 := (@ZPow.toPow.{0} Complex Gram666ProofSharing.c240)

noncomputable def Gram666ProofSharing.c242 := (@instHPow.{0, 0} Complex Int Gram666ProofSharing.c241)

noncomputable def Gram666ProofSharing.c243 := (@OfNat.ofNat.{0} Int (nat_lit 1) (@instOfNat (nat_lit 1)))

noncomputable def Gram666ProofSharing.c244 := (@OfNat.ofNat.{0} Int (nat_lit 2) (@instOfNat (nat_lit 2)))

noncomputable def Gram666ProofSharing.c245 := (nat_lit 14202233028597258339323424675647)

noncomputable def Gram666ProofSharing.c246 := (nat_lit 16138982698097381747775689293641140947)

noncomputable def Gram666ProofSharing.c247 := (BSN.w_sub_half_zero_mk Gram666ProofSharing.c39 Bool.false (nat_lit 102273270) (nat_lit 100000) Gram666ProofSharing.c56 (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram666ProofSharing.c248 := (Enclosure.sfrac Bool.true (nat_lit 100000) (nat_lit 400000))

noncomputable def Gram666ProofSharing.c249 := (Enclosure.Real.IsNear.const Bool.true (nat_lit 100000) (nat_lit 400000))

noncomputable def Gram666ProofSharing.c250 := (@Enclosure.Complex.IsNear.mk Gram666ProofSharing.c248 Gram666ProofSharing.c59 Bool.true (nat_lit 100000) (nat_lit 400000) (nat_lit 0) (nat_lit 1) Bool.false (nat_lit 204546540) (nat_lit 400000) (nat_lit 0) (nat_lit 1) Gram666ProofSharing.c249 Gram666ProofSharing.c61)

noncomputable def Gram666ProofSharing.c251 := (@Enclosure.Complex.IsNear.of_eq Gram666ProofSharing.c234 { re := Enclosure.sfrac Bool.true (nat_lit 100000) (nat_lit 400000), im := Enclosure.sfrac Bool.false (nat_lit 204546540) (nat_lit 400000) } Bool.true (nat_lit 100000) (nat_lit 400000) (nat_lit 0) (nat_lit 1) Bool.false (nat_lit 204546540) (nat_lit 400000) (nat_lit 0) (nat_lit 1) Gram666ProofSharing.c247 Gram666ProofSharing.c250)

noncomputable def Gram666ProofSharing.c252 := (@Enclosure.Complex.IsNear.re_isNear Gram666ProofSharing.c234 Bool.true (nat_lit 100000) (nat_lit 400000) (nat_lit 0) (nat_lit 1) Bool.false (nat_lit 204546540) (nat_lit 400000) (nat_lit 0) (nat_lit 1) Gram666ProofSharing.c251)

noncomputable def Gram666ProofSharing.c253 := (Complex.log { re := Enclosure.sfrac Bool.false (nat_lit 100000) (nat_lit 400000), im := Enclosure.sfrac Bool.false (nat_lit 204546540) (nat_lit 400000) })

noncomputable def Gram666ProofSharing.c254 := (@congrArg.{1, 1} Complex Complex Gram666ProofSharing.c47 { re := Enclosure.sfrac Bool.false (nat_lit 100000) (nat_lit 400000), im := Enclosure.sfrac Bool.false (nat_lit 204546540) (nat_lit 400000) } Complex.log Gram666ProofSharing.c57)

noncomputable def Gram666ProofSharing.c255 := (Enclosure.sfrac Bool.false (nat_lit 1) (nat_lit 2))

noncomputable def Gram666ProofSharing.c256 := (Enclosure.sfrac Bool.false (nat_lit 41839297025971600) (nat_lit 160000000000))

noncomputable def Gram666ProofSharing.c257 := (Real.log Gram666ProofSharing.c256)

noncomputable def Gram666ProofSharing.c258 := (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) Gram666ProofSharing.c255 Gram666ProofSharing.c257)

noncomputable def Gram666ProofSharing.c259 := (Enclosure.clog_re_eq (nat_lit 100000) (nat_lit 204546540) (nat_lit 400000) (nat_lit 41839297025971600) (nat_lit 160000000000) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram666ProofSharing.c260 := (Enclosure.Real.IsNear.const Bool.false (nat_lit 1) (nat_lit 2))

noncomputable def Gram666ProofSharing.c261 := (@Nat.cast.{0} Real Real.instNatCast (nat_lit 41839297025971600))

noncomputable def Gram666ProofSharing.c262 := (@Nat.cast.{0} Real Real.instNatCast (nat_lit 160000000000))

noncomputable def Gram666ProofSharing.c263 := (@HDiv.hDiv.{0, 0, 0} Real Real Real Gram666ProofSharing.c15 Gram666ProofSharing.c261 Gram666ProofSharing.c262)

noncomputable def Gram666ProofSharing.c264 := (Real.log Gram666ProofSharing.c263)

noncomputable def Gram666ProofSharing.c265 := (nat_lit 12559425513603832152993403184579370151040452707461030131438470886294022979394933526096618935683158146958505164374013087080025484269096466533568371381607331441297498557316848211316235680553854857136961747381917640170983916397797090530605092551408531685400024179101244300336893851751465072106854095217754112000000000000000000000000000000000000000000)

noncomputable def Gram666ProofSharing.c266 := (nat_lit 495339563988606161829029162449534944570121404127000527782418123249299430356722743863584091803300129578702550969446367588612764309687897473374599774967096628540832835520028061845290521613516259848918506808762917603721505977409589089792307609861371099922343775688828884912971438005534382031693591067439923200000000000000000000000000000000000000000)

noncomputable def Gram666ProofSharing.c267 := (nat_lit 160540783944655756694615220408229010423284741921379891244507453615064924925067249445605111595309373630476292753873532692673359501663571516676310959547393727176392064233535257071706242662612756096029118099670371385892361565583008121742160976975900998508957218259190928127486827158128430438940672000000000000000000000000000000000000000000)

noncomputable def Gram666ProofSharing.c268 := (BSN.artanhP (nat_lit 20867777025971600))

noncomputable def Gram666ProofSharing.c269 := (BSN.artanhQ (nat_lit 62810817025971600))

noncomputable def Gram666ProofSharing.c270 := (@BSN.binarySplit_of_base10 Gram666ProofSharing.c268 Gram666ProofSharing.c269 (nat_lit 0) (nat_lit 10) Gram666ProofSharing.c266 Gram666ProofSharing.c265 Gram666ProofSharing.c267 (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram666ProofSharing.c271 := (BSN.log_dyadic_bound (nat_lit 20867777025971600) (nat_lit 62810817025971600) (nat_lit 11) (nat_lit 10) Gram666ProofSharing.c265 (nat_lit 17179869184) (nat_lit 6800000000) Gram666ProofSharing.c266 Gram666ProofSharing.c267 (nat_lit 11865632126) (nat_lit 83678594051943200) (nat_lit 41943040000000000) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) Gram666ProofSharing.c270 (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram666ProofSharing.c272 := (BSN.log_rat_reduce_isNear (nat_lit 41839297025971600) (nat_lit 160000000000) (nat_lit 17) (nat_lit 83678594051943200) (nat_lit 41943040000000000) (nat_lit 11865632126) (nat_lit 17179869184) (nat_lit 24973259072661432) (nat_lit 36028797018963968) (nat_lit 6800000000) (nat_lit 1000000000000000) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) Gram666ProofSharing.c271 BSN.log2_near_15 (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram666ProofSharing.c273 := (@Enclosure.Real.IsNear.recentre' Gram666ProofSharing.c264 Bool.false (nat_lit 7721138958799249282133131264) (nat_lit 618970019642690137449562112) (nat_lit 1000115600000000) (nat_lit 6800000000000000000000000) (nat_lit 56178679797443687) (nat_lit 4503599627370496) (nat_lit 2500289) (nat_lit 17000000000000000) Gram666ProofSharing.c272 (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram666ProofSharing.c274 := (BSN.isNear_log_sfrac (nat_lit 41839297025971600) (nat_lit 160000000000) (nat_lit 56178679797443687) (nat_lit 4503599627370496) (nat_lit 2500289) (nat_lit 17000000000000000) Bool.false Gram666ProofSharing.c273)

noncomputable def Gram666ProofSharing.c275 := (@Enclosure.Real.IsNear.mulLit_ff Gram666ProofSharing.c255 Gram666ProofSharing.c257 (nat_lit 1) (nat_lit 2) (nat_lit 0) (nat_lit 1) (nat_lit 56178679797443687) (nat_lit 4503599627370496) (nat_lit 2500289) (nat_lit 17000000000000000) (nat_lit 56178679797443687) (nat_lit 9007199254740992) (nat_lit 2500289) (nat_lit 34000000000000000) Gram666ProofSharing.c260 Gram666ProofSharing.c274 (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram666ProofSharing.c276 := (@Enclosure.Real.IsNear.of_eq (Gram666ProofSharing.c253 : ℂ).re Gram666ProofSharing.c258 Bool.false (nat_lit 56178679797443687) (nat_lit 9007199254740992) (nat_lit 2500289) (nat_lit 34000000000000000) Gram666ProofSharing.c259 Gram666ProofSharing.c275)

noncomputable def Gram666ProofSharing.c277 := (@Nat.cast.{0} Real Real.instNatCast (nat_lit 204546540))

noncomputable def Gram666ProofSharing.c278 := (@Nat.cast.{0} Real Real.instNatCast (nat_lit 100000))

noncomputable def Gram666ProofSharing.c279 := (@HDiv.hDiv.{0, 0, 0} Real Real Real Gram666ProofSharing.c15 Gram666ProofSharing.c277 Gram666ProofSharing.c278)

noncomputable def Gram666ProofSharing.c280 := (Real.arctan Gram666ProofSharing.c279)

noncomputable def Gram666ProofSharing.c281 := (Enclosure.clog_im_eq (nat_lit 100000) (nat_lit 204546540) (nat_lit 400000) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram666ProofSharing.c282 := (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) Gram666ProofSharing.c255 Real.pi)

noncomputable def Gram666ProofSharing.c283 := (@HDiv.hDiv.{0, 0, 0} Real Real Real Gram666ProofSharing.c15 Gram666ProofSharing.c278 Gram666ProofSharing.c277)

noncomputable def Gram666ProofSharing.c284 := (Real.arctan Gram666ProofSharing.c283)

noncomputable def Gram666ProofSharing.c285 := (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) Gram666ProofSharing.c282 Gram666ProofSharing.c284)

noncomputable def Gram666ProofSharing.c286 := (BSN.arctan_recip (nat_lit 204546540) (nat_lit 100000) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram666ProofSharing.c287 := (@Enclosure.Real.IsNear.mulLit_ff Gram666ProofSharing.c255 Real.pi (nat_lit 1) (nat_lit 2) (nat_lit 0) (nat_lit 1) (nat_lit 226375608064910080) (nat_lit 72057594037927936) (nat_lit 1) (nat_lit 1000000000000000) (nat_lit 884279719003555) (nat_lit 562949953421312) (nat_lit 1) (nat_lit 2000000000000000) Gram666ProofSharing.c260 BSN.pi_near_15 (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram666ProofSharing.c288 := (@BSN.binarySplit_of_le (BSN.arctanEvenP (nat_lit 100000)) (BSN.arctanEvenQ (nat_lit 204546540)) (nat_lit 0) (nat_lit 0) (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram666ProofSharing.c289 := (@BSN.binarySplit_of_le (BSN.arctanOddP (nat_lit 100000)) (BSN.arctanOddQ (nat_lit 204546540)) (nat_lit 0) (nat_lit 0) (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram666ProofSharing.c290 := (BSN.arctan_dyadic_bound_f (nat_lit 100000) (nat_lit 204546540) (nat_lit 1) (nat_lit 0) (nat_lit 17179869184) (nat_lit 6800000000) (nat_lit 0) (nat_lit 1) (nat_lit 1) (nat_lit 0) (nat_lit 1) (nat_lit 1) (nat_lit 8399001) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) Gram666ProofSharing.c288 Gram666ProofSharing.c289 (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram666ProofSharing.c291 := (@Enclosure.Real.IsNear.subLit_ff_p Gram666ProofSharing.c282 Gram666ProofSharing.c284 (nat_lit 884279719003555) (nat_lit 562949953421312) (nat_lit 1) (nat_lit 2000000000000000) (nat_lit 8399001) (nat_lit 17179869184) (nat_lit 1) (nat_lit 6800000000) (nat_lit 15187081677323618178039808) (nat_lit 884004500538787) (nat_lit 562949953421312) (nat_lit 5000017) (nat_lit 34000000000000000) Gram666ProofSharing.c287 Gram666ProofSharing.c290 (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram666ProofSharing.c292 := (@Enclosure.Real.IsNear.of_eq Gram666ProofSharing.c280 Gram666ProofSharing.c285 Bool.false (nat_lit 884004500538787) (nat_lit 562949953421312) (nat_lit 5000017) (nat_lit 34000000000000000) Gram666ProofSharing.c286 Gram666ProofSharing.c291)

noncomputable def Gram666ProofSharing.c293 := (@Enclosure.Real.IsNear.of_eq (Gram666ProofSharing.c253 : ℂ).im Gram666ProofSharing.c280 Bool.false (nat_lit 884004500538787) (nat_lit 562949953421312) (nat_lit 5000017) (nat_lit 34000000000000000) Gram666ProofSharing.c281 Gram666ProofSharing.c292)

noncomputable def Gram666ProofSharing.c294 := (@Enclosure.Complex.IsNear.of_parts Gram666ProofSharing.c253 Bool.false (nat_lit 56178679797443687) (nat_lit 9007199254740992) (nat_lit 2500289) (nat_lit 34000000000000000) Bool.false (nat_lit 884004500538787) (nat_lit 562949953421312) (nat_lit 5000017) (nat_lit 34000000000000000) Gram666ProofSharing.c276 Gram666ProofSharing.c293)

noncomputable def Gram666ProofSharing.c295 := (@Enclosure.Complex.IsNear.of_eq Gram666ProofSharing.c235 Gram666ProofSharing.c253 Bool.false (nat_lit 56178679797443687) (nat_lit 9007199254740992) (nat_lit 2500289) (nat_lit 34000000000000000) Bool.false (nat_lit 884004500538787) (nat_lit 562949953421312) (nat_lit 5000017) (nat_lit 34000000000000000) Gram666ProofSharing.c254 Gram666ProofSharing.c294)

noncomputable def Gram666ProofSharing.c296 := (@Enclosure.Complex.IsNear.re_isNear Gram666ProofSharing.c235 Bool.false (nat_lit 56178679797443687) (nat_lit 9007199254740992) (nat_lit 2500289) (nat_lit 34000000000000000) Bool.false (nat_lit 884004500538787) (nat_lit 562949953421312) (nat_lit 5000017) (nat_lit 34000000000000000) Gram666ProofSharing.c295)

noncomputable def Gram666ProofSharing.c297 := (@Enclosure.Complex.IsNear.im_isNear Gram666ProofSharing.c234 Bool.true (nat_lit 100000) (nat_lit 400000) (nat_lit 0) (nat_lit 1) Bool.false (nat_lit 204546540) (nat_lit 400000) (nat_lit 0) (nat_lit 1) Gram666ProofSharing.c251)

noncomputable def Gram666ProofSharing.c298 := (@Enclosure.Complex.IsNear.im_isNear Gram666ProofSharing.c235 Bool.false (nat_lit 56178679797443687) (nat_lit 9007199254740992) (nat_lit 2500289) (nat_lit 34000000000000000) Bool.false (nat_lit 884004500538787) (nat_lit 562949953421312) (nat_lit 5000017) (nat_lit 34000000000000000) Gram666ProofSharing.c295)

noncomputable def Gram666ProofSharing.c299 := (↑Gram666ProofSharing.c8)

noncomputable def Gram666ProofSharing.c300 := (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) (Gram666ProofSharing.c233 : ℂ).re (Gram666ProofSharing.c299 : ℂ).re)

noncomputable def Gram666ProofSharing.c301 := (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) (Gram666ProofSharing.c233 : ℂ).im (Gram666ProofSharing.c299 : ℂ).im)

noncomputable def Gram666ProofSharing.c302 := (Enclosure.sfrac Bool.false (nat_lit 0) (nat_lit 1))

noncomputable def Gram666ProofSharing.c303 := (Enclosure.Real.IsNear.const Bool.false (nat_lit 0) (nat_lit 1))

noncomputable def Gram666ProofSharing.c304 := (@Enclosure.Complex.IsNear.mk Gram666ProofSharing.c255 Gram666ProofSharing.c302 Bool.false (nat_lit 1) (nat_lit 2) (nat_lit 0) (nat_lit 1) Bool.false (nat_lit 0) (nat_lit 1) (nat_lit 0) (nat_lit 1) Gram666ProofSharing.c260 Gram666ProofSharing.c303)

noncomputable def Gram666ProofSharing.c305 := (@Enclosure.Complex.IsNear.of_eq Gram666ProofSharing.c233 { re := Enclosure.sfrac Bool.false (nat_lit 1) (nat_lit 2), im := Enclosure.sfrac Bool.false (nat_lit 0) (nat_lit 1) } Bool.false (nat_lit 1) (nat_lit 2) (nat_lit 0) (nat_lit 1) Bool.false (nat_lit 0) (nat_lit 1) (nat_lit 0) (nat_lit 1) BSN.half_c_mk Gram666ProofSharing.c304)

noncomputable def Gram666ProofSharing.c306 := (@Enclosure.Complex.IsNear.re_isNear Gram666ProofSharing.c233 Bool.false (nat_lit 1) (nat_lit 2) (nat_lit 0) (nat_lit 1) Bool.false (nat_lit 0) (nat_lit 1) (nat_lit 0) (nat_lit 1) Gram666ProofSharing.c305)

noncomputable def Gram666ProofSharing.c307 := (Complex.ofReal_re Gram666ProofSharing.c8)

noncomputable def Gram666ProofSharing.c308 := (@Enclosure.Real.IsNear.of_eq (Gram666ProofSharing.c299 : ℂ).re Gram666ProofSharing.c8 Bool.false (nat_lit 3946810947) (nat_lit 2147483648) (nat_lit 1) (nat_lit 4294967296) Gram666ProofSharing.c307 Zeta.Certificates.Gram.gp12_cert._proof_1)

noncomputable def Gram666ProofSharing.c309 := (@Enclosure.Real.IsNear.mulLit_ff (Gram666ProofSharing.c233 : ℂ).re (Gram666ProofSharing.c299 : ℂ).re (nat_lit 1) (nat_lit 2) (nat_lit 0) (nat_lit 1) (nat_lit 3946810947) (nat_lit 2147483648) (nat_lit 1) (nat_lit 4294967296) (nat_lit 3946810947) (nat_lit 4294967296) (nat_lit 1) (nat_lit 8589934592) Gram666ProofSharing.c306 Gram666ProofSharing.c308 (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram666ProofSharing.c310 := (@Enclosure.Complex.IsNear.im_isNear Gram666ProofSharing.c233 Bool.false (nat_lit 1) (nat_lit 2) (nat_lit 0) (nat_lit 1) Bool.false (nat_lit 0) (nat_lit 1) (nat_lit 0) (nat_lit 1) Gram666ProofSharing.c305)

noncomputable def Gram666ProofSharing.c311 := (Complex.ofReal_im Gram666ProofSharing.c8)

noncomputable def Gram666ProofSharing.c312 := (@Eq.trans.{1} Real (Gram666ProofSharing.c299 : ℂ).im Gram666ProofSharing.c147 Gram666ProofSharing.c302 Gram666ProofSharing.c311 Enclosure.sfrac_zero_eq)

noncomputable def Gram666ProofSharing.c313 := (@Enclosure.Real.IsNear.of_eq (Gram666ProofSharing.c299 : ℂ).im Gram666ProofSharing.c302 Bool.false (nat_lit 0) (nat_lit 1) (nat_lit 0) (nat_lit 1) Gram666ProofSharing.c312 Gram666ProofSharing.c303)

noncomputable def Gram666ProofSharing.c314 := (@Enclosure.Real.IsNear.mulLit_ff (Gram666ProofSharing.c233 : ℂ).im (Gram666ProofSharing.c299 : ℂ).im (nat_lit 0) (nat_lit 1) (nat_lit 0) (nat_lit 1) (nat_lit 0) (nat_lit 1) (nat_lit 0) (nat_lit 1) (nat_lit 0) (nat_lit 1) (nat_lit 0) (nat_lit 1) Gram666ProofSharing.c310 Gram666ProofSharing.c313 (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram666ProofSharing.c315 := (@Enclosure.Real.IsNear.subLit_ff_p Gram666ProofSharing.c300 Gram666ProofSharing.c301 (nat_lit 3946810947) (nat_lit 4294967296) (nat_lit 1) (nat_lit 8589934592) (nat_lit 0) (nat_lit 1) (nat_lit 0) (nat_lit 1) (nat_lit 3946810947) (nat_lit 3946810947) (nat_lit 4294967296) (nat_lit 1) (nat_lit 8589934592) Gram666ProofSharing.c309 Gram666ProofSharing.c314 (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram666ProofSharing.c316 := (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) (Gram666ProofSharing.c233 : ℂ).re (Gram666ProofSharing.c299 : ℂ).im)

noncomputable def Gram666ProofSharing.c317 := (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) (Gram666ProofSharing.c233 : ℂ).im (Gram666ProofSharing.c299 : ℂ).re)

noncomputable def Gram666ProofSharing.c318 := (@Enclosure.Real.IsNear.mulLit_ff (Gram666ProofSharing.c233 : ℂ).re (Gram666ProofSharing.c299 : ℂ).im (nat_lit 1) (nat_lit 2) (nat_lit 0) (nat_lit 1) (nat_lit 0) (nat_lit 1) (nat_lit 0) (nat_lit 1) (nat_lit 0) (nat_lit 1) (nat_lit 0) (nat_lit 1) Gram666ProofSharing.c306 Gram666ProofSharing.c313 (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram666ProofSharing.c319 := (@Enclosure.Real.IsNear.mulLit_ff (Gram666ProofSharing.c233 : ℂ).im (Gram666ProofSharing.c299 : ℂ).re (nat_lit 0) (nat_lit 1) (nat_lit 0) (nat_lit 1) (nat_lit 3946810947) (nat_lit 2147483648) (nat_lit 1) (nat_lit 4294967296) (nat_lit 0) (nat_lit 1) (nat_lit 0) (nat_lit 1) Gram666ProofSharing.c310 Gram666ProofSharing.c308 (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram666ProofSharing.c320 := (@Enclosure.Real.IsNear.addLit_ff Gram666ProofSharing.c316 Gram666ProofSharing.c317 (nat_lit 0) (nat_lit 1) (nat_lit 0) (nat_lit 1) (nat_lit 0) (nat_lit 1) (nat_lit 0) (nat_lit 1) (nat_lit 0) (nat_lit 0) (nat_lit 1) (nat_lit 0) (nat_lit 1) Gram666ProofSharing.c318 Gram666ProofSharing.c319 (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram666ProofSharing.c321 := (@Enclosure.Complex.IsNear.mul Gram666ProofSharing.c233 Gram666ProofSharing.c299 Bool.false (nat_lit 3946810947) (nat_lit 4294967296) (nat_lit 1) (nat_lit 8589934592) Bool.false (nat_lit 0) (nat_lit 1) (nat_lit 0) (nat_lit 1) Gram666ProofSharing.c315 Gram666ProofSharing.c320)

noncomputable def Gram666ProofSharing.c322 := (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) Gram666ProofSharing.c32 (nat_lit 2))

noncomputable def Gram666ProofSharing.c323 := (bernoulli Gram666ProofSharing.c322)

noncomputable def Gram666ProofSharing.c324 := (@Rat.cast.{0} Complex Complex.instRatCast Gram666ProofSharing.c323)

noncomputable def Gram666ProofSharing.c325 := (@Nat.cast.{0} Complex Complex.instNatCast (nat_lit 2))

noncomputable def Gram666ProofSharing.c326 := (@HMul.hMul.{0, 0, 0} Complex Complex Complex (@instHMul.{0} Complex Complex.instMul) Gram666ProofSharing.c42 Gram666ProofSharing.c325)

noncomputable def Gram666ProofSharing.c327 := (@HSub.hSub.{0, 0, 0} Complex Complex Complex (@instHSub.{0} Complex Complex.instSub) Gram666ProofSharing.c326 Gram666ProofSharing.c30)

noncomputable def Gram666ProofSharing.c328 := (@HMul.hMul.{0, 0, 0} Complex Complex Complex (@instHMul.{0} Complex Complex.instMul) Gram666ProofSharing.c326 Gram666ProofSharing.c327)

noncomputable def Gram666ProofSharing.c329 := (@HDiv.hDiv.{0, 0, 0} Complex Complex Complex Gram666ProofSharing.c28 Gram666ProofSharing.c324 Gram666ProofSharing.c328)

noncomputable def Gram666ProofSharing.c330 := (@Nat.cast.{0} Int instNatCastInt (nat_lit 2))

noncomputable def Gram666ProofSharing.c331 := (@HMul.hMul.{0, 0, 0} Int Int Int (@instHMul.{0} Int Int.instMul) Gram666ProofSharing.c244 Gram666ProofSharing.c330)

noncomputable def Gram666ProofSharing.c332 := (@HSub.hSub.{0, 0, 0} Int Int Int (@instHSub.{0} Int Int.instSub) Gram666ProofSharing.c243 Gram666ProofSharing.c331)

noncomputable def Gram666ProofSharing.c333 := (@HPow.hPow.{0, 0, 0} Complex Int Complex Gram666ProofSharing.c242 Gram666ProofSharing.c47 Gram666ProofSharing.c332)

noncomputable def Gram666ProofSharing.c334 := (@HMul.hMul.{0, 0, 0} Complex Complex Complex (@instHMul.{0} Complex Complex.instMul) Gram666ProofSharing.c329 Gram666ProofSharing.c333)

noncomputable def Gram666ProofSharing.c335 := (nat_lit 2057264037429548864077641140947)

noncomputable def Gram666ProofSharing.c336 := (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) Gram666ProofSharing.c32 (nat_lit 1))

noncomputable def Gram666ProofSharing.c337 := (bernoulli Gram666ProofSharing.c336)

noncomputable def Gram666ProofSharing.c338 := (@Rat.cast.{0} Complex Complex.instRatCast Gram666ProofSharing.c337)

noncomputable def Gram666ProofSharing.c339 := (@Nat.cast.{0} Complex Complex.instNatCast (nat_lit 1))

noncomputable def Gram666ProofSharing.c340 := (@HMul.hMul.{0, 0, 0} Complex Complex Complex (@instHMul.{0} Complex Complex.instMul) Gram666ProofSharing.c42 Gram666ProofSharing.c339)

noncomputable def Gram666ProofSharing.c341 := (@HSub.hSub.{0, 0, 0} Complex Complex Complex (@instHSub.{0} Complex Complex.instSub) Gram666ProofSharing.c340 Gram666ProofSharing.c30)

noncomputable def Gram666ProofSharing.c342 := (@HMul.hMul.{0, 0, 0} Complex Complex Complex (@instHMul.{0} Complex Complex.instMul) Gram666ProofSharing.c340 Gram666ProofSharing.c341)

noncomputable def Gram666ProofSharing.c343 := (@HDiv.hDiv.{0, 0, 0} Complex Complex Complex Gram666ProofSharing.c28 Gram666ProofSharing.c338 Gram666ProofSharing.c342)

noncomputable def Gram666ProofSharing.c344 := (@Nat.cast.{0} Int instNatCastInt (nat_lit 1))

noncomputable def Gram666ProofSharing.c345 := (@HMul.hMul.{0, 0, 0} Int Int Int (@instHMul.{0} Int Int.instMul) Gram666ProofSharing.c244 Gram666ProofSharing.c344)

noncomputable def Gram666ProofSharing.c346 := (@HSub.hSub.{0, 0, 0} Int Int Int (@instHSub.{0} Int Int.instSub) Gram666ProofSharing.c243 Gram666ProofSharing.c345)

noncomputable def Gram666ProofSharing.c347 := (@HPow.hPow.{0, 0, 0} Complex Int Complex Gram666ProofSharing.c242 Gram666ProofSharing.c47 Gram666ProofSharing.c346)

noncomputable def Gram666ProofSharing.c348 := (@HMul.hMul.{0, 0, 0} Complex Complex Complex (@instHMul.{0} Complex Complex.instMul) Gram666ProofSharing.c343 Gram666ProofSharing.c347)

noncomputable def Gram666ProofSharing.c349 := (@Enclosure.Complex.IsNear.mk Gram666ProofSharing.c302 Gram666ProofSharing.c302 Bool.false (nat_lit 0) (nat_lit 1) (nat_lit 0) (nat_lit 1) Bool.false (nat_lit 0) (nat_lit 1) (nat_lit 0) (nat_lit 1) Gram666ProofSharing.c303 Gram666ProofSharing.c303)

noncomputable def Gram666ProofSharing.c350 := (BSN.stirling_coeff_mk (nat_lit 1) (nat_lit 1) (nat_lit 6) Bool.false BSN.bern_real_1 (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram666ProofSharing.c351 := (Enclosure.sfrac Bool.false (nat_lit 1) (nat_lit 12))

noncomputable def Gram666ProofSharing.c352 := (Enclosure.Real.IsNear.const Bool.false (nat_lit 1) (nat_lit 12))

noncomputable def Gram666ProofSharing.c353 := (@Enclosure.Complex.IsNear.mk Gram666ProofSharing.c351 Gram666ProofSharing.c302 Bool.false (nat_lit 1) (nat_lit 12) (nat_lit 0) (nat_lit 1) Bool.false (nat_lit 0) (nat_lit 1) (nat_lit 0) (nat_lit 1) Gram666ProofSharing.c352 Gram666ProofSharing.c303)

noncomputable def Gram666ProofSharing.c354 := (@Enclosure.Complex.IsNear.of_eq Gram666ProofSharing.c343 { re := Enclosure.sfrac Bool.false (nat_lit 1) (nat_lit 12), im := Enclosure.sfrac Bool.false (nat_lit 0) (nat_lit 1) } Bool.false (nat_lit 1) (nat_lit 12) (nat_lit 0) (nat_lit 1) Bool.false (nat_lit 0) (nat_lit 1) (nat_lit 0) (nat_lit 1) Gram666ProofSharing.c350 Gram666ProofSharing.c353)

noncomputable def Gram666ProofSharing.c355 := (@Enclosure.Complex.IsNear.re_isNear Gram666ProofSharing.c343 Bool.false (nat_lit 1) (nat_lit 12) (nat_lit 0) (nat_lit 1) Bool.false (nat_lit 0) (nat_lit 1) (nat_lit 0) (nat_lit 1) Gram666ProofSharing.c354)

noncomputable def Gram666ProofSharing.c356 := (@Inv.inv.{0} Complex Complex.instInv Gram666ProofSharing.c50)

noncomputable def Gram666ProofSharing.c357 := (BSN.zpow_one_sub_two_mul Gram666ProofSharing.c47 (nat_lit 1) (nat_lit 1) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram666ProofSharing.c358 := (@instMulZeroOneClassOfSemiring.{0} Complex Complex.instSemiring)

noncomputable def Gram666ProofSharing.c359 := (@instMulZeroOneClassOfSemiring.{0} Real Real.semiring)

noncomputable def Gram666ProofSharing.c360 := (@MonoidWithZeroHom.{0, 0} Complex Real Gram666ProofSharing.c358 Gram666ProofSharing.c359)

noncomputable def Gram666ProofSharing.c361 := (@MonoidWithZeroHom.funLike.{0, 0} Complex Real Gram666ProofSharing.c358 Gram666ProofSharing.c359)

noncomputable def Gram666ProofSharing.c362 := (Enclosure.Complex.inv_re_eq_mul Gram666ProofSharing.c50)

noncomputable def Gram666ProofSharing.c363 := (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) (Gram666ProofSharing.c50 : ℂ).re (Gram666ProofSharing.c50 : ℂ).re)

noncomputable def Gram666ProofSharing.c364 := (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) (Gram666ProofSharing.c50 : ℂ).im (Gram666ProofSharing.c50 : ℂ).im)

noncomputable def Gram666ProofSharing.c365 := (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd) Gram666ProofSharing.c363 Gram666ProofSharing.c364)

noncomputable def Gram666ProofSharing.c366 := (Enclosure.Complex.normSq_eq_mul_add_mul Gram666ProofSharing.c50)

noncomputable def Gram666ProofSharing.c367 := (@Enclosure.Real.IsNear.mulLit_ff (Gram666ProofSharing.c50 : ℂ).re (Gram666ProofSharing.c50 : ℂ).re (nat_lit 100000) (nat_lit 400000) (nat_lit 0) (nat_lit 1) (nat_lit 100000) (nat_lit 400000) (nat_lit 0) (nat_lit 1) (nat_lit 1) (nat_lit 16) (nat_lit 0) (nat_lit 1) Gram666ProofSharing.c65 Gram666ProofSharing.c65 (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram666ProofSharing.c368 := (@Enclosure.Real.IsNear.mulLit_ff (Gram666ProofSharing.c50 : ℂ).im (Gram666ProofSharing.c50 : ℂ).im (nat_lit 204546540) (nat_lit 400000) (nat_lit 0) (nat_lit 1) (nat_lit 204546540) (nat_lit 400000) (nat_lit 0) (nat_lit 1) (nat_lit 104598217564929) (nat_lit 400000000) (nat_lit 0) (nat_lit 1) Gram666ProofSharing.c68 Gram666ProofSharing.c68 (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram666ProofSharing.c369 := (@Enclosure.Real.IsNear.addLit_ff Gram666ProofSharing.c363 Gram666ProofSharing.c364 (nat_lit 1) (nat_lit 16) (nat_lit 0) (nat_lit 1) (nat_lit 104598217564929) (nat_lit 400000000) (nat_lit 0) (nat_lit 1) (nat_lit 1673571881038864) (nat_lit 104598242564929) (nat_lit 400000000) (nat_lit 0) (nat_lit 1) Gram666ProofSharing.c367 Gram666ProofSharing.c368 (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram666ProofSharing.c370 := (@Neg.neg.{0} Real Real.instNeg (Gram666ProofSharing.c50 : ℂ).im)

noncomputable def Gram666ProofSharing.c371 := (Enclosure.Complex.inv_im_eq_mul Gram666ProofSharing.c50)

noncomputable def Gram666ProofSharing.c372 := (@Enclosure.Real.IsNear.neg (Gram666ProofSharing.c50 : ℂ).im Bool.false (nat_lit 204546540) (nat_lit 400000) (nat_lit 0) (nat_lit 1) Gram666ProofSharing.c68)

noncomputable def Gram666ProofSharing.c373 := (@Enclosure.Complex.IsNear.im_isNear Gram666ProofSharing.c343 Bool.false (nat_lit 1) (nat_lit 12) (nat_lit 0) (nat_lit 1) Bool.false (nat_lit 0) (nat_lit 1) (nat_lit 0) (nat_lit 1) Gram666ProofSharing.c354)

noncomputable def Gram666ProofSharing.c374 := (nat_lit 495176015714152109959649689600000000)

noncomputable def Gram666ProofSharing.c375 := (BSN.stirling_coeff_mk (nat_lit 2) (nat_lit 1) (nat_lit 30) Bool.true BSN.bern_real_2 (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram666ProofSharing.c376 := (Enclosure.sfrac Bool.true (nat_lit 1) (nat_lit 360))

noncomputable def Gram666ProofSharing.c377 := (Enclosure.Real.IsNear.const Bool.true (nat_lit 1) (nat_lit 360))

noncomputable def Gram666ProofSharing.c378 := (@Enclosure.Complex.IsNear.mk Gram666ProofSharing.c376 Gram666ProofSharing.c302 Bool.true (nat_lit 1) (nat_lit 360) (nat_lit 0) (nat_lit 1) Bool.false (nat_lit 0) (nat_lit 1) (nat_lit 0) (nat_lit 1) Gram666ProofSharing.c377 Gram666ProofSharing.c303)

noncomputable def Gram666ProofSharing.c379 := (@Enclosure.Complex.IsNear.of_eq Gram666ProofSharing.c329 { re := Enclosure.sfrac Bool.true (nat_lit 1) (nat_lit 360), im := Enclosure.sfrac Bool.false (nat_lit 0) (nat_lit 1) } Bool.true (nat_lit 1) (nat_lit 360) (nat_lit 0) (nat_lit 1) Bool.false (nat_lit 0) (nat_lit 1) (nat_lit 0) (nat_lit 1) Gram666ProofSharing.c375 Gram666ProofSharing.c378)

noncomputable def Gram666ProofSharing.c380 := (@Enclosure.Complex.IsNear.re_isNear Gram666ProofSharing.c329 Bool.true (nat_lit 1) (nat_lit 360) (nat_lit 0) (nat_lit 1) Bool.false (nat_lit 0) (nat_lit 1) (nat_lit 0) (nat_lit 1) Gram666ProofSharing.c379)

noncomputable def Gram666ProofSharing.c381 := (nat_lit 18515376336865939776698770268523)

noncomputable def Gram666ProofSharing.c382 := (nat_lit 2475880078570760549798248448000000000000)

noncomputable def Gram666ProofSharing.c383 := (@Inv.inv.{0} Complex Complex.instInv Gram666ProofSharing.c48)

noncomputable def Gram666ProofSharing.c384 := (BSN.zpow_one_sub_two_mul Gram666ProofSharing.c47 (nat_lit 2) (nat_lit 3) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram666ProofSharing.c385 := (Enclosure.Complex.inv_re_eq_mul Gram666ProofSharing.c48)

noncomputable def Gram666ProofSharing.c386 := (@Enclosure.Complex.IsNear.re_isNear Gram666ProofSharing.c48 Bool.true (nat_lit 313794627694787) (nat_lit 1600000000) (nat_lit 0) (nat_lit 1) Bool.true (nat_lit 1069759407604147614783) (nat_lit 8000000000000) (nat_lit 0) (nat_lit 1) Zeta.Certificates.Gram.gp12_cert._proof_2)

noncomputable def Gram666ProofSharing.c387 := (nat_lit 1144387651834286090376059908484372385137089)

noncomputable def Gram666ProofSharing.c388 := (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) (Gram666ProofSharing.c48 : ℂ).re (Gram666ProofSharing.c48 : ℂ).re)

noncomputable def Gram666ProofSharing.c389 := (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) (Gram666ProofSharing.c48 : ℂ).im (Gram666ProofSharing.c48 : ℂ).im)

noncomputable def Gram666ProofSharing.c390 := (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd) Gram666ProofSharing.c388 Gram666ProofSharing.c389)

noncomputable def Gram666ProofSharing.c391 := (Enclosure.Complex.normSq_eq_mul_add_mul Gram666ProofSharing.c48)

noncomputable def Gram666ProofSharing.c392 := (nat_lit 1144385190157576837626447367809988160137089)

noncomputable def Gram666ProofSharing.c393 := (nat_lit 2929632388695772391362713365719993305950947840000000000000000)

noncomputable def Gram666ProofSharing.c394 := (@Enclosure.Real.IsNear.mulLit_tt (Gram666ProofSharing.c48 : ℂ).re (Gram666ProofSharing.c48 : ℂ).re (nat_lit 313794627694787) (nat_lit 1600000000) (nat_lit 0) (nat_lit 1) (nat_lit 313794627694787) (nat_lit 1600000000) (nat_lit 0) (nat_lit 1) (nat_lit 98467068370109984501626975369) (nat_lit 2560000000000000000) (nat_lit 0) (nat_lit 1) Gram666ProofSharing.c386 Gram666ProofSharing.c386 (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram666ProofSharing.c395 := (@Enclosure.Complex.IsNear.im_isNear Gram666ProofSharing.c48 Bool.true (nat_lit 313794627694787) (nat_lit 1600000000) (nat_lit 0) (nat_lit 1) Bool.true (nat_lit 1069759407604147614783) (nat_lit 8000000000000) (nat_lit 0) (nat_lit 1) Zeta.Certificates.Gram.gp12_cert._proof_2)

noncomputable def Gram666ProofSharing.c396 := (@Enclosure.Real.IsNear.mulLit_tt (Gram666ProofSharing.c48 : ℂ).im (Gram666ProofSharing.c48 : ℂ).im (nat_lit 1069759407604147614783) (nat_lit 8000000000000) (nat_lit 0) (nat_lit 1) (nat_lit 1069759407604147614783) (nat_lit 8000000000000) (nat_lit 0) (nat_lit 1) Gram666ProofSharing.c392 (nat_lit 64000000000000000000000000) (nat_lit 0) (nat_lit 1) Gram666ProofSharing.c395 Gram666ProofSharing.c395 (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram666ProofSharing.c397 := (@Enclosure.Real.IsNear.addLit_ff Gram666ProofSharing.c388 Gram666ProofSharing.c389 (nat_lit 98467068370109984501626975369) (nat_lit 2560000000000000000) (nat_lit 0) (nat_lit 1) Gram666ProofSharing.c392 (nat_lit 64000000000000000000000000) (nat_lit 0) (nat_lit 1) Gram666ProofSharing.c393 Gram666ProofSharing.c387 (nat_lit 64000000000000000000000000) (nat_lit 0) (nat_lit 1) Gram666ProofSharing.c394 Gram666ProofSharing.c396 (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram666ProofSharing.c398 := (@Neg.neg.{0} Real Real.instNeg (Gram666ProofSharing.c48 : ℂ).im)

noncomputable def Gram666ProofSharing.c399 := (Enclosure.Complex.inv_im_eq_mul Gram666ProofSharing.c48)

noncomputable def Gram666ProofSharing.c400 := (@Enclosure.Real.IsNear.neg (Gram666ProofSharing.c48 : ℂ).im Bool.true (nat_lit 1069759407604147614783) (nat_lit 8000000000000) (nat_lit 0) (nat_lit 1) Gram666ProofSharing.c395)

noncomputable def Gram666ProofSharing.c401 := (@Enclosure.Complex.IsNear.im_isNear Gram666ProofSharing.c329 Bool.true (nat_lit 1) (nat_lit 360) (nat_lit 0) (nat_lit 1) Bool.false (nat_lit 0) (nat_lit 1) (nat_lit 0) (nat_lit 1) Gram666ProofSharing.c379)

noncomputable def Gram666ProofSharing.c402 := (BSN.logSumC Gram666ProofSharing.c39 (nat_lit 0))

noncomputable def Gram666ProofSharing.c403 := (Enclosure.sfrac Bool.false (nat_lit 98304000000000000000000000) Gram666ProofSharing.c106)

noncomputable def Gram666ProofSharing.c404 := (@Monoid.toNPow.{0} Real Real.instMonoid)

noncomputable def Gram666ProofSharing.c405 := (@NPow.toPow.{0} Real Gram666ProofSharing.c404)

noncomputable def Gram666ProofSharing.c406 := (@instHPow.{0, 0} Real Nat Gram666ProofSharing.c405)

noncomputable def Gram666ProofSharing.c407 := (@HPow.hPow.{0, 0, 0} Real Nat Real Gram666ProofSharing.c406 Gram666ProofSharing.c7 (nat_lit 4))

noncomputable def Gram666ProofSharing.c408 := (@Inv.inv.{0} Real Real.instInv Gram666ProofSharing.c407)

noncomputable def Gram666ProofSharing.c409 := (nat_lit 611446774371975769155682509262542103857872115376664175900625)

noncomputable def Gram666ProofSharing.c410 := (nat_lit 392318858461667547739736838950479151006397215279002157056)

noncomputable def Gram666ProofSharing.c411 := (nat_lit 19652562622312316682495810535216024035134795670488584765154486969712234385047)

noncomputable def Gram666ProofSharing.c412 := (nat_lit 9903520314283042199192993792000000000000000000000000000000000000000000000000000000000000)

noncomputable def Gram666ProofSharing.c413 := (@HPow.hPow.{0, 0, 0} Real Nat Real Gram666ProofSharing.c406 Gram666ProofSharing.c7 (nat_lit 3))

noncomputable def Gram666ProofSharing.c414 := (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) Gram666ProofSharing.c413 Gram666ProofSharing.c7)

noncomputable def Gram666ProofSharing.c415 := (BSN.pow_succ_r Gram666ProofSharing.c7 (nat_lit 3) (nat_lit 4) (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram666ProofSharing.c416 := (nat_lit 691463075802508163054686763366652189853178875)

noncomputable def Gram666ProofSharing.c417 := (nat_lit 2787593149816327892691964784081045188247552)

noncomputable def Gram666ProofSharing.c418 := (nat_lit 2184744797947834540264818678394244808492865883128339)

noncomputable def Gram666ProofSharing.c419 := (nat_lit 9223372036854775808000000000000000000000000000000000000000000000)

noncomputable def Gram666ProofSharing.c420 := (@HPow.hPow.{0, 0, 0} Real Nat Real Gram666ProofSharing.c406 Gram666ProofSharing.c7 (nat_lit 2))

noncomputable def Gram666ProofSharing.c421 := (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) Gram666ProofSharing.c420 Gram666ProofSharing.c7)

noncomputable def Gram666ProofSharing.c422 := (BSN.pow_succ_r Gram666ProofSharing.c7 (nat_lit 2) (nat_lit 3) (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram666ProofSharing.c423 := (nat_lit 1073741824000000000000000000000000000000)

noncomputable def Gram666ProofSharing.c424 := (@HPow.hPow.{0, 0, 0} Real Nat Real Gram666ProofSharing.c406 Gram666ProofSharing.c7 (nat_lit 1))

noncomputable def Gram666ProofSharing.c425 := (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) Gram666ProofSharing.c424 Gram666ProofSharing.c7)

noncomputable def Gram666ProofSharing.c426 := (BSN.pow_succ_r Gram666ProofSharing.c7 (nat_lit 1) (nat_lit 2) (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram666ProofSharing.c427 := (BSN.pow_one_r Gram666ProofSharing.c7)

noncomputable def Gram666ProofSharing.c428 := (@Enclosure.Real.IsNear.of_eq Gram666ProofSharing.c7 Gram666ProofSharing.c10 Bool.false (nat_lit 884279719003555) (nat_lit 140737488355328) (nat_lit 1) (nat_lit 500000000000000) BSN.two_pi_eq Gram666ProofSharing.c13)

noncomputable def Gram666ProofSharing.c429 := (@Enclosure.Real.IsNear.of_eq Gram666ProofSharing.c424 Gram666ProofSharing.c7 Bool.false (nat_lit 884279719003555) (nat_lit 140737488355328) (nat_lit 1) (nat_lit 500000000000000) Gram666ProofSharing.c427 Gram666ProofSharing.c428)

noncomputable def Gram666ProofSharing.c430 := (@Enclosure.Real.IsNear.mulLit_ff Gram666ProofSharing.c424 Gram666ProofSharing.c7 (nat_lit 884279719003555) (nat_lit 140737488355328) (nat_lit 1) (nat_lit 500000000000000) (nat_lit 884279719003555) (nat_lit 140737488355328) (nat_lit 1) (nat_lit 500000000000000) (nat_lit 781950621441006189802102638025) (nat_lit 19807040628566084398385987584) (nat_lit 26986075409044041160201671) Gram666ProofSharing.c423 Gram666ProofSharing.c429 Gram666ProofSharing.c428 (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram666ProofSharing.c431 := (@Enclosure.Real.IsNear.of_eq Gram666ProofSharing.c420 Gram666ProofSharing.c425 Bool.false (nat_lit 781950621441006189802102638025) (nat_lit 19807040628566084398385987584) (nat_lit 26986075409044041160201671) Gram666ProofSharing.c423 Gram666ProofSharing.c426 Gram666ProofSharing.c430)

noncomputable def Gram666ProofSharing.c432 := (@Enclosure.Real.IsNear.mulLit_ff Gram666ProofSharing.c420 Gram666ProofSharing.c7 (nat_lit 781950621441006189802102638025) (nat_lit 19807040628566084398385987584) (nat_lit 26986075409044041160201671) Gram666ProofSharing.c423 (nat_lit 884279719003555) (nat_lit 140737488355328) (nat_lit 1) (nat_lit 500000000000000) Gram666ProofSharing.c416 Gram666ProofSharing.c417 Gram666ProofSharing.c418 Gram666ProofSharing.c419 Gram666ProofSharing.c431 Gram666ProofSharing.c428 (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram666ProofSharing.c433 := (@Enclosure.Real.IsNear.of_eq Gram666ProofSharing.c413 Gram666ProofSharing.c421 Bool.false Gram666ProofSharing.c416 Gram666ProofSharing.c417 Gram666ProofSharing.c418 Gram666ProofSharing.c419 Gram666ProofSharing.c422 Gram666ProofSharing.c432)

noncomputable def Gram666ProofSharing.c434 := (@Enclosure.Real.IsNear.mulLit_ff Gram666ProofSharing.c413 Gram666ProofSharing.c7 Gram666ProofSharing.c416 Gram666ProofSharing.c417 Gram666ProofSharing.c418 Gram666ProofSharing.c419 (nat_lit 884279719003555) (nat_lit 140737488355328) (nat_lit 1) (nat_lit 500000000000000) Gram666ProofSharing.c409 Gram666ProofSharing.c410 Gram666ProofSharing.c411 Gram666ProofSharing.c412 Gram666ProofSharing.c433 Gram666ProofSharing.c428 (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram666ProofSharing.c435 := (@Enclosure.Real.IsNear.of_eq Gram666ProofSharing.c407 Gram666ProofSharing.c414 Bool.false Gram666ProofSharing.c409 Gram666ProofSharing.c410 Gram666ProofSharing.c411 Gram666ProofSharing.c412 Gram666ProofSharing.c415 Gram666ProofSharing.c434)

noncomputable def Gram666ProofSharing.c436 := (@Enclosure.Real.IsNear.inv_image Gram666ProofSharing.c407 Gram666ProofSharing.c409 Gram666ProofSharing.c410 Gram666ProofSharing.c411 Gram666ProofSharing.c412 (nat_lit 5511507) (nat_lit 5511508) (nat_lit 8589934592) Gram666ProofSharing.c435 (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram666ProofSharing.c437 := (@Enclosure.Real.IsNear.recentre' Gram666ProofSharing.c408 Bool.false (nat_lit 11023015) (nat_lit 17179869184) (nat_lit 1) (nat_lit 17179869184) (nat_lit 11023015) (nat_lit 17179869184) (nat_lit 1) (nat_lit 17179869184) Gram666ProofSharing.c436 (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram666ProofSharing.c438 := (nat_lit 650790500585593272939861641254656179389)

noncomputable def Gram666ProofSharing.c439 := (nat_lit 19807040628566084398385987584000000000000000)

noncomputable def Gram666ProofSharing.c440 := (nat_lit 164891648131246035461114214301599784254241)

noncomputable def Gram666ProofSharing.c441 := (nat_lit 1052249033392573233664255590400000000000000000000)

noncomputable def Gram666ProofSharing.c442 := (nat_lit 1750526981021487634566560382973456)

noncomputable def Gram666ProofSharing.c443 := (riemannSiegelThetaApproximant (nat_lit 2) (nat_lit 0) Gram666ProofSharing.c107)

noncomputable def Gram666ProofSharing.c444 := (nat_lit 41442285767276974660983691556181641254656179389)

noncomputable def Gram666ProofSharing.c445 := (nat_lit 164890947333389796007340593907376577854241)

noncomputable def Gram666ProofSharing.c446 := (Complex.Stirling.logGammaStirling (nat_lit 2) Gram666ProofSharing.c112)

noncomputable def Gram666ProofSharing.c447 := (@HDiv.hDiv.{0, 0, 0} Real Real Real Gram666ProofSharing.c15 Gram666ProofSharing.c107 Gram666ProofSharing.c6)

noncomputable def Gram666ProofSharing.c448 := (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) Gram666ProofSharing.c447 (Real.log Real.pi))

noncomputable def Gram666ProofSharing.c449 := (nat_lit 53036859124225422440681417385067022374656179389)

noncomputable def Gram666ProofSharing.c450 := (nat_lit 39608325558398801408813617907376577854241)

noncomputable def Gram666ProofSharing.c451 := (nat_lit 955364170703403587854370406250033496845837)

noncomputable def Gram666ProofSharing.c452 := (nat_lit 1188422437713965063903159255040000000000)

noncomputable def Gram666ProofSharing.c453 := (nat_lit 44590626142549899151351669931735960134127)

noncomputable def Gram666ProofSharing.c454 := (nat_lit 591890081283322443936143769600000000000000000000)

noncomputable def Gram666ProofSharing.c455 := (@HSub.hSub.{0, 0, 0} Complex Complex Complex (@instHSub.{0} Complex Complex.instSub) Gram666ProofSharing.c112 Gram666ProofSharing.c233)

noncomputable def Gram666ProofSharing.c456 := (Complex.log Gram666ProofSharing.c112)

noncomputable def Gram666ProofSharing.c457 := (@HMul.hMul.{0, 0, 0} Complex Complex Complex (@instHMul.{0} Complex Complex.instMul) Gram666ProofSharing.c455 Gram666ProofSharing.c456)

noncomputable def Gram666ProofSharing.c458 := (@HSub.hSub.{0, 0, 0} Complex Complex Complex (@instHSub.{0} Complex Complex.instSub) Gram666ProofSharing.c457 Gram666ProofSharing.c112)

noncomputable def Gram666ProofSharing.c459 := (@HAdd.hAdd.{0, 0, 0} Complex Complex Complex (@instHAdd.{0} Complex Complex.instAdd) Gram666ProofSharing.c458 Gram666ProofSharing.c238)

noncomputable def Gram666ProofSharing.c460 := (nat_lit 94681547960448637765019712754163)

noncomputable def Gram666ProofSharing.c461 := (nat_lit 17826336565709475958547388825600000000000)

noncomputable def Gram666ProofSharing.c462 := (nat_lit 3227796444634189614867198900185343820611)

noncomputable def Gram666ProofSharing.c463 := (nat_lit 99035203142830421991929937920000000000000000)

noncomputable def Gram666ProofSharing.c464 := (BSN.w_sub_half_zero_mk Gram666ProofSharing.c107 Bool.false (nat_lit 102273273) (nat_lit 100000) Gram666ProofSharing.c121 (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram666ProofSharing.c465 := (@Enclosure.Complex.IsNear.mk Gram666ProofSharing.c248 Gram666ProofSharing.c123 Bool.true (nat_lit 100000) (nat_lit 400000) (nat_lit 0) (nat_lit 1) Bool.false (nat_lit 204546546) (nat_lit 400000) (nat_lit 0) (nat_lit 1) Gram666ProofSharing.c249 Gram666ProofSharing.c124)

noncomputable def Gram666ProofSharing.c466 := (@Enclosure.Complex.IsNear.of_eq Gram666ProofSharing.c455 { re := Enclosure.sfrac Bool.true (nat_lit 100000) (nat_lit 400000), im := Enclosure.sfrac Bool.false (nat_lit 204546546) (nat_lit 400000) } Bool.true (nat_lit 100000) (nat_lit 400000) (nat_lit 0) (nat_lit 1) Bool.false (nat_lit 204546546) (nat_lit 400000) (nat_lit 0) (nat_lit 1) Gram666ProofSharing.c464 Gram666ProofSharing.c465)

noncomputable def Gram666ProofSharing.c467 := (@Enclosure.Complex.IsNear.re_isNear Gram666ProofSharing.c455 Bool.true (nat_lit 100000) (nat_lit 400000) (nat_lit 0) (nat_lit 1) Bool.false (nat_lit 204546546) (nat_lit 400000) (nat_lit 0) (nat_lit 1) Gram666ProofSharing.c466)

noncomputable def Gram666ProofSharing.c468 := (Complex.log { re := Enclosure.sfrac Bool.false (nat_lit 100000) (nat_lit 400000), im := Enclosure.sfrac Bool.false (nat_lit 204546546) (nat_lit 400000) })

noncomputable def Gram666ProofSharing.c469 := (@congrArg.{1, 1} Complex Complex Gram666ProofSharing.c112 { re := Enclosure.sfrac Bool.false (nat_lit 100000) (nat_lit 400000), im := Enclosure.sfrac Bool.false (nat_lit 204546546) (nat_lit 400000) } Complex.log Gram666ProofSharing.c122)

noncomputable def Gram666ProofSharing.c470 := (Enclosure.sfrac Bool.false (nat_lit 41839299480530116) (nat_lit 160000000000))

noncomputable def Gram666ProofSharing.c471 := (Real.log Gram666ProofSharing.c470)

noncomputable def Gram666ProofSharing.c472 := (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) Gram666ProofSharing.c255 Gram666ProofSharing.c471)

noncomputable def Gram666ProofSharing.c473 := (Enclosure.clog_re_eq (nat_lit 100000) (nat_lit 204546546) (nat_lit 400000) (nat_lit 41839299480530116) (nat_lit 160000000000) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram666ProofSharing.c474 := (@Nat.cast.{0} Real Real.instNatCast (nat_lit 41839299480530116))

noncomputable def Gram666ProofSharing.c475 := (@HDiv.hDiv.{0, 0, 0} Real Real Real Gram666ProofSharing.c15 Gram666ProofSharing.c474 Gram666ProofSharing.c262)

noncomputable def Gram666ProofSharing.c476 := (Real.log Gram666ProofSharing.c475)

noncomputable def Gram666ProofSharing.c477 := (nat_lit 12559435329701681182413524601660939148817042166579992637412634141772768453534009266603730880473952011453730017064445747366047075458563700078344154200506346241623746335369238810652031211943673099768278465781466445033302635766993636814346058232373456854018439145673718026359415715449899367454941020763127071816621681457600490621431754543565321011200)

noncomputable def Gram666ProofSharing.c478 := (nat_lit 495340034622423579886143165990474610064539021912639977931371791253246708442094791023394965484890069778825200902488750962866999874131998671746364424285667407758616938462646940601423348701352713494438699562125473428686681119190282139565638190719851409631198297999782024305118740657533464999074096554659849303100534806397149997558327872070164152320)

noncomputable def Gram666ProofSharing.c479 := (nat_lit 160541161615155338769117606094233198537649296547991915080049133287868640007968272605821914869528931785195811036749757935544335242365431242372305021732114799580305928140597559888843181753116884782430050221900006608313146637278537472175348648251108949742468940154949010781512986352878923148846065179786976005035592400852236570645967667200)

noncomputable def Gram666ProofSharing.c480 := (BSN.artanhP (nat_lit 20867779480530116))

noncomputable def Gram666ProofSharing.c481 := (BSN.artanhQ (nat_lit 62810819480530116))

noncomputable def Gram666ProofSharing.c482 := (@BSN.binarySplit_of_base10 Gram666ProofSharing.c480 Gram666ProofSharing.c481 (nat_lit 0) (nat_lit 10) Gram666ProofSharing.c478 Gram666ProofSharing.c477 Gram666ProofSharing.c479 (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram666ProofSharing.c483 := (BSN.log_dyadic_bound (nat_lit 20867779480530116) (nat_lit 62810819480530116) (nat_lit 11) (nat_lit 10) Gram666ProofSharing.c477 (nat_lit 17179869184) (nat_lit 6800000000) Gram666ProofSharing.c478 Gram666ProofSharing.c479 (nat_lit 11865633134) (nat_lit 83678598961060232) (nat_lit 41943040000000000) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) Gram666ProofSharing.c482 (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram666ProofSharing.c484 := (BSN.log_rat_reduce_isNear (nat_lit 41839299480530116) (nat_lit 160000000000) (nat_lit 17) (nat_lit 83678598961060232) (nat_lit 41943040000000000) (nat_lit 11865633134) (nat_lit 17179869184) (nat_lit 24973259072661432) (nat_lit 36028797018963968) (nat_lit 6800000000) (nat_lit 1000000000000000) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) Gram666ProofSharing.c483 BSN.log2_near_15 (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram666ProofSharing.c485 := (@Enclosure.Real.IsNear.recentre' Gram666ProofSharing.c476 Bool.false (nat_lit 7721138995116276677248811008) (nat_lit 618970019642690137449562112) (nat_lit 1000115600000000) (nat_lit 6800000000000000000000000) (nat_lit 56178680061684839) (nat_lit 4503599627370496) (nat_lit 2500289) (nat_lit 17000000000000000) Gram666ProofSharing.c484 (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram666ProofSharing.c486 := (BSN.isNear_log_sfrac (nat_lit 41839299480530116) (nat_lit 160000000000) (nat_lit 56178680061684839) (nat_lit 4503599627370496) (nat_lit 2500289) (nat_lit 17000000000000000) Bool.false Gram666ProofSharing.c485)

noncomputable def Gram666ProofSharing.c487 := (@Enclosure.Real.IsNear.mulLit_ff Gram666ProofSharing.c255 Gram666ProofSharing.c471 (nat_lit 1) (nat_lit 2) (nat_lit 0) (nat_lit 1) (nat_lit 56178680061684839) (nat_lit 4503599627370496) (nat_lit 2500289) (nat_lit 17000000000000000) (nat_lit 56178680061684839) (nat_lit 9007199254740992) (nat_lit 2500289) (nat_lit 34000000000000000) Gram666ProofSharing.c260 Gram666ProofSharing.c486 (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram666ProofSharing.c488 := (@Enclosure.Real.IsNear.of_eq (Gram666ProofSharing.c468 : ℂ).re Gram666ProofSharing.c472 Bool.false (nat_lit 56178680061684839) (nat_lit 9007199254740992) (nat_lit 2500289) (nat_lit 34000000000000000) Gram666ProofSharing.c473 Gram666ProofSharing.c487)

noncomputable def Gram666ProofSharing.c489 := (@Nat.cast.{0} Real Real.instNatCast (nat_lit 204546546))

noncomputable def Gram666ProofSharing.c490 := (@HDiv.hDiv.{0, 0, 0} Real Real Real Gram666ProofSharing.c15 Gram666ProofSharing.c489 Gram666ProofSharing.c278)

noncomputable def Gram666ProofSharing.c491 := (Real.arctan Gram666ProofSharing.c490)

noncomputable def Gram666ProofSharing.c492 := (Enclosure.clog_im_eq (nat_lit 100000) (nat_lit 204546546) (nat_lit 400000) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram666ProofSharing.c493 := (@HDiv.hDiv.{0, 0, 0} Real Real Real Gram666ProofSharing.c15 Gram666ProofSharing.c278 Gram666ProofSharing.c489)

noncomputable def Gram666ProofSharing.c494 := (Real.arctan Gram666ProofSharing.c493)

noncomputable def Gram666ProofSharing.c495 := (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) Gram666ProofSharing.c282 Gram666ProofSharing.c494)

noncomputable def Gram666ProofSharing.c496 := (BSN.arctan_recip (nat_lit 204546546) (nat_lit 100000) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram666ProofSharing.c497 := (@BSN.binarySplit_of_le (BSN.arctanEvenP (nat_lit 100000)) (BSN.arctanEvenQ (nat_lit 204546546)) (nat_lit 0) (nat_lit 0) (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram666ProofSharing.c498 := (@BSN.binarySplit_of_le (BSN.arctanOddP (nat_lit 100000)) (BSN.arctanOddQ (nat_lit 204546546)) (nat_lit 0) (nat_lit 0) (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram666ProofSharing.c499 := (BSN.arctan_dyadic_bound_f (nat_lit 100000) (nat_lit 204546546) (nat_lit 1) (nat_lit 0) (nat_lit 17179869184) (nat_lit 6800000000) (nat_lit 0) (nat_lit 1) (nat_lit 1) (nat_lit 0) (nat_lit 1) (nat_lit 1) (nat_lit 8399001) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) Gram666ProofSharing.c497 Gram666ProofSharing.c498 (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram666ProofSharing.c500 := (@Enclosure.Real.IsNear.subLit_ff_p Gram666ProofSharing.c282 Gram666ProofSharing.c494 (nat_lit 884279719003555) (nat_lit 562949953421312) (nat_lit 1) (nat_lit 2000000000000000) (nat_lit 8399001) (nat_lit 17179869184) (nat_lit 1) (nat_lit 6800000000) (nat_lit 15187081677323618178039808) (nat_lit 884004500538787) (nat_lit 562949953421312) (nat_lit 5000017) (nat_lit 34000000000000000) Gram666ProofSharing.c287 Gram666ProofSharing.c499 (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram666ProofSharing.c501 := (@Enclosure.Real.IsNear.of_eq Gram666ProofSharing.c491 Gram666ProofSharing.c495 Bool.false (nat_lit 884004500538787) (nat_lit 562949953421312) (nat_lit 5000017) (nat_lit 34000000000000000) Gram666ProofSharing.c496 Gram666ProofSharing.c500)

noncomputable def Gram666ProofSharing.c502 := (@Enclosure.Real.IsNear.of_eq (Gram666ProofSharing.c468 : ℂ).im Gram666ProofSharing.c491 Bool.false (nat_lit 884004500538787) (nat_lit 562949953421312) (nat_lit 5000017) (nat_lit 34000000000000000) Gram666ProofSharing.c492 Gram666ProofSharing.c501)

noncomputable def Gram666ProofSharing.c503 := (@Enclosure.Complex.IsNear.of_parts Gram666ProofSharing.c468 Bool.false (nat_lit 56178680061684839) (nat_lit 9007199254740992) (nat_lit 2500289) (nat_lit 34000000000000000) Bool.false (nat_lit 884004500538787) (nat_lit 562949953421312) (nat_lit 5000017) (nat_lit 34000000000000000) Gram666ProofSharing.c488 Gram666ProofSharing.c502)

noncomputable def Gram666ProofSharing.c504 := (@Enclosure.Complex.IsNear.of_eq Gram666ProofSharing.c456 Gram666ProofSharing.c468 Bool.false (nat_lit 56178680061684839) (nat_lit 9007199254740992) (nat_lit 2500289) (nat_lit 34000000000000000) Bool.false (nat_lit 884004500538787) (nat_lit 562949953421312) (nat_lit 5000017) (nat_lit 34000000000000000) Gram666ProofSharing.c469 Gram666ProofSharing.c503)

noncomputable def Gram666ProofSharing.c505 := (@Enclosure.Complex.IsNear.re_isNear Gram666ProofSharing.c456 Bool.false (nat_lit 56178680061684839) (nat_lit 9007199254740992) (nat_lit 2500289) (nat_lit 34000000000000000) Bool.false (nat_lit 884004500538787) (nat_lit 562949953421312) (nat_lit 5000017) (nat_lit 34000000000000000) Gram666ProofSharing.c504)

noncomputable def Gram666ProofSharing.c506 := (@Enclosure.Complex.IsNear.im_isNear Gram666ProofSharing.c455 Bool.true (nat_lit 100000) (nat_lit 400000) (nat_lit 0) (nat_lit 1) Bool.false (nat_lit 204546546) (nat_lit 400000) (nat_lit 0) (nat_lit 1) Gram666ProofSharing.c466)

noncomputable def Gram666ProofSharing.c507 := (@Enclosure.Complex.IsNear.im_isNear Gram666ProofSharing.c456 Bool.false (nat_lit 56178680061684839) (nat_lit 9007199254740992) (nat_lit 2500289) (nat_lit 34000000000000000) Bool.false (nat_lit 884004500538787) (nat_lit 562949953421312) (nat_lit 5000017) (nat_lit 34000000000000000) Gram666ProofSharing.c504)

noncomputable def Gram666ProofSharing.c508 := (@HPow.hPow.{0, 0, 0} Complex Int Complex Gram666ProofSharing.c242 Gram666ProofSharing.c112 Gram666ProofSharing.c332)

noncomputable def Gram666ProofSharing.c509 := (@HMul.hMul.{0, 0, 0} Complex Complex Complex (@instHMul.{0} Complex Complex.instMul) Gram666ProofSharing.c329 Gram666ProofSharing.c508)

noncomputable def Gram666ProofSharing.c510 := (nat_lit 411452771282751008405465343820611)

noncomputable def Gram666ProofSharing.c511 := (@HPow.hPow.{0, 0, 0} Complex Int Complex Gram666ProofSharing.c242 Gram666ProofSharing.c112 Gram666ProofSharing.c346)

noncomputable def Gram666ProofSharing.c512 := (@HMul.hMul.{0, 0, 0} Complex Complex Complex (@instHMul.{0} Complex Complex.instMul) Gram666ProofSharing.c343 Gram666ProofSharing.c511)

noncomputable def Gram666ProofSharing.c513 := (@Inv.inv.{0} Complex Complex.instInv Gram666ProofSharing.c115)

noncomputable def Gram666ProofSharing.c514 := (BSN.zpow_one_sub_two_mul Gram666ProofSharing.c112 (nat_lit 1) (nat_lit 1) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram666ProofSharing.c515 := (Enclosure.Complex.inv_re_eq_mul Gram666ProofSharing.c115)

noncomputable def Gram666ProofSharing.c516 := (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) (Gram666ProofSharing.c115 : ℂ).re (Gram666ProofSharing.c115 : ℂ).re)

noncomputable def Gram666ProofSharing.c517 := (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) (Gram666ProofSharing.c115 : ℂ).im (Gram666ProofSharing.c115 : ℂ).im)

noncomputable def Gram666ProofSharing.c518 := (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd) Gram666ProofSharing.c516 Gram666ProofSharing.c517)

noncomputable def Gram666ProofSharing.c519 := (Enclosure.Complex.normSq_eq_mul_add_mul Gram666ProofSharing.c115)

noncomputable def Gram666ProofSharing.c520 := (@Enclosure.Real.IsNear.mulLit_ff (Gram666ProofSharing.c115 : ℂ).re (Gram666ProofSharing.c115 : ℂ).re (nat_lit 100000) (nat_lit 400000) (nat_lit 0) (nat_lit 1) (nat_lit 100000) (nat_lit 400000) (nat_lit 0) (nat_lit 1) (nat_lit 1) (nat_lit 16) (nat_lit 0) (nat_lit 1) Gram666ProofSharing.c128 Gram666ProofSharing.c128 (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram666ProofSharing.c521 := (@Enclosure.Real.IsNear.mulLit_ff (Gram666ProofSharing.c115 : ℂ).im (Gram666ProofSharing.c115 : ℂ).im (nat_lit 204546546) (nat_lit 400000) (nat_lit 0) (nat_lit 1) (nat_lit 204546546) (nat_lit 400000) (nat_lit 0) (nat_lit 1) (nat_lit 10459822370132529) (nat_lit 40000000000) (nat_lit 0) (nat_lit 1) Gram666ProofSharing.c131 Gram666ProofSharing.c131 (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram666ProofSharing.c522 := (@Enclosure.Real.IsNear.addLit_ff Gram666ProofSharing.c516 Gram666ProofSharing.c517 (nat_lit 1) (nat_lit 16) (nat_lit 0) (nat_lit 1) (nat_lit 10459822370132529) (nat_lit 40000000000) (nat_lit 0) (nat_lit 1) (nat_lit 167357197922120464) (nat_lit 10459824870132529) (nat_lit 40000000000) (nat_lit 0) (nat_lit 1) Gram666ProofSharing.c520 Gram666ProofSharing.c521 (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram666ProofSharing.c523 := (@Neg.neg.{0} Real Real.instNeg (Gram666ProofSharing.c115 : ℂ).im)

noncomputable def Gram666ProofSharing.c524 := (Enclosure.Complex.inv_im_eq_mul Gram666ProofSharing.c115)

noncomputable def Gram666ProofSharing.c525 := (@Enclosure.Real.IsNear.neg (Gram666ProofSharing.c115 : ℂ).im Bool.false (nat_lit 204546546) (nat_lit 400000) (nat_lit 0) (nat_lit 1) Gram666ProofSharing.c131)

noncomputable def Gram666ProofSharing.c526 := (nat_lit 9903520314283042199192993792000000000)

noncomputable def Gram666ProofSharing.c527 := (nat_lit 49517601571415210995964968960000000000)

noncomputable def Gram666ProofSharing.c528 := (nat_lit 3703074941544759075649188094385499)

noncomputable def Gram666ProofSharing.c529 := (nat_lit 495176015714152109959649689600000000000000)

noncomputable def Gram666ProofSharing.c530 := (nat_lit 2475880078570760549798248448000000000000000)

noncomputable def Gram666ProofSharing.c531 := (@Inv.inv.{0} Complex Complex.instInv Gram666ProofSharing.c113)

noncomputable def Gram666ProofSharing.c532 := (BSN.zpow_one_sub_two_mul Gram666ProofSharing.c112 (nat_lit 2) (nat_lit 3) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram666ProofSharing.c533 := (Enclosure.Complex.inv_re_eq_mul Gram666ProofSharing.c113)

noncomputable def Gram666ProofSharing.c534 := (@Enclosure.Complex.IsNear.re_isNear Gram666ProofSharing.c113 Bool.true (nat_lit 31379464610397587) (nat_lit 160000000000) (nat_lit 0) (nat_lit 1) Bool.true (nat_lit 1069759501742523684597417) (nat_lit 8000000000000000) (nat_lit 0) (nat_lit 1) Zeta.Certificates.Gram.gp12_cert._proof_6)

noncomputable def Gram666ProofSharing.c535 := (nat_lit 1144387853245410622169036043681496956227863071889)

noncomputable def Gram666ProofSharing.c536 := (nat_lit 64000000000000000000000000000000)

noncomputable def Gram666ProofSharing.c537 := (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) (Gram666ProofSharing.c113 : ℂ).re (Gram666ProofSharing.c113 : ℂ).re)

noncomputable def Gram666ProofSharing.c538 := (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) (Gram666ProofSharing.c113 : ℂ).im (Gram666ProofSharing.c113 : ℂ).im)

noncomputable def Gram666ProofSharing.c539 := (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd) Gram666ProofSharing.c537 Gram666ProofSharing.c538)

noncomputable def Gram666ProofSharing.c540 := (Enclosure.Complex.normSq_eq_mul_add_mul Gram666ProofSharing.c113)

noncomputable def Gram666ProofSharing.c541 := (nat_lit 984670799235194586491950215422569)

noncomputable def Gram666ProofSharing.c542 := (nat_lit 1144385391568412534182569813805958399805363071889)

noncomputable def Gram666ProofSharing.c543 := (nat_lit 29296329043082511927527322718246322079433294640358400000000000000000000)

noncomputable def Gram666ProofSharing.c544 := (@Enclosure.Real.IsNear.mulLit_tt (Gram666ProofSharing.c113 : ℂ).re (Gram666ProofSharing.c113 : ℂ).re (nat_lit 31379464610397587) (nat_lit 160000000000) (nat_lit 0) (nat_lit 1) (nat_lit 31379464610397587) (nat_lit 160000000000) (nat_lit 0) (nat_lit 1) Gram666ProofSharing.c541 (nat_lit 25600000000000000000000) (nat_lit 0) (nat_lit 1) Gram666ProofSharing.c534 Gram666ProofSharing.c534 (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram666ProofSharing.c545 := (@Enclosure.Complex.IsNear.im_isNear Gram666ProofSharing.c113 Bool.true (nat_lit 31379464610397587) (nat_lit 160000000000) (nat_lit 0) (nat_lit 1) Bool.true (nat_lit 1069759501742523684597417) (nat_lit 8000000000000000) (nat_lit 0) (nat_lit 1) Zeta.Certificates.Gram.gp12_cert._proof_6)

noncomputable def Gram666ProofSharing.c546 := (@Enclosure.Real.IsNear.mulLit_tt (Gram666ProofSharing.c113 : ℂ).im (Gram666ProofSharing.c113 : ℂ).im (nat_lit 1069759501742523684597417) (nat_lit 8000000000000000) (nat_lit 0) (nat_lit 1) (nat_lit 1069759501742523684597417) (nat_lit 8000000000000000) (nat_lit 0) (nat_lit 1) Gram666ProofSharing.c542 Gram666ProofSharing.c536 (nat_lit 0) (nat_lit 1) Gram666ProofSharing.c545 Gram666ProofSharing.c545 (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram666ProofSharing.c547 := (@Enclosure.Real.IsNear.addLit_ff Gram666ProofSharing.c537 Gram666ProofSharing.c538 Gram666ProofSharing.c541 (nat_lit 25600000000000000000000) (nat_lit 0) (nat_lit 1) Gram666ProofSharing.c542 Gram666ProofSharing.c536 (nat_lit 0) (nat_lit 1) Gram666ProofSharing.c543 Gram666ProofSharing.c535 Gram666ProofSharing.c536 (nat_lit 0) (nat_lit 1) Gram666ProofSharing.c544 Gram666ProofSharing.c546 (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram666ProofSharing.c548 := (@Neg.neg.{0} Real Real.instNeg (Gram666ProofSharing.c113 : ℂ).im)

noncomputable def Gram666ProofSharing.c549 := (Enclosure.Complex.inv_im_eq_mul Gram666ProofSharing.c113)

noncomputable def Gram666ProofSharing.c550 := (@Enclosure.Real.IsNear.neg (Gram666ProofSharing.c113 : ℂ).im Bool.true (nat_lit 1069759501742523684597417) (nat_lit 8000000000000000) (nat_lit 0) (nat_lit 1) Gram666ProofSharing.c545)

noncomputable def Gram666ProofSharing.c551 := (BSN.logSumC Gram666ProofSharing.c107 (nat_lit 0))

noncomputable def Gram666ProofSharing.c552 := (Enclosure.sfrac Bool.false (nat_lit 98304000000000000000000000) Gram666ProofSharing.c144)


