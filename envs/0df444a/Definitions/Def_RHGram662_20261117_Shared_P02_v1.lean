-- Prove2me | Definitions.Def_RHGram662_20261117_Shared_P02_v1
-- name    : RHGram662_20261117_Shared_P02_v1
-- status  : Definition
-- author  : @bueno_ricardo
-- created : 2026-11-17T23:15:05.768442+00:00
-- url     : https://prove2.me/theorems/60862e26-de87-4d61-9c0d-f131b2048704
-- title:
--   Gram 662 ordinary shared terms, part 2
-- statement:
--   Exact shared expressions and complete ordinary auxiliary proofs for the endpoint certificate of Gram point 662. No additional axioms or custom proof generators. Imports the already published analytic and numerical support modules.
-- source:
--   Salvatore Mercuri and Bhavik Mehta, smmercuri/zeta commit 3dab6480a82f1bfc5de0a59550e279cf50490033; Apache-2.0. Ordinary proof export and exact sharing by Desenvolvimento RH. Full expanded strict AXLE and cumulative prefixes: 0d72a449-68eb-451e-baac-4003d630c3da.

import Definitions.Def_RHGram662_20261117_Shared_P01_v1
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
noncomputable def Gram662ProofSharing.c227 := (nat_lit 263659881598523992776488234461593487214160369583)

noncomputable def Gram662ProofSharing.c228 := (nat_lit 78834297847197510932554850234527580328001)

noncomputable def Gram662ProofSharing.c229 := (nat_lit 14261308540155747740162440632594768795078253)

noncomputable def Gram662ProofSharing.c230 := (nat_lit 17826336565709475958547388825600000000000)

noncomputable def Gram662ProofSharing.c231 := (nat_lit 29582464296953287931874916563968939092949)

noncomputable def Gram662ProofSharing.c232 := (nat_lit 382987699653914522546916556800000000000000000000)

noncomputable def Gram662ProofSharing.c233 := (@HDiv.hDiv.{0, 0, 0} Complex Complex Complex Gram662ProofSharing.c28 Gram662ProofSharing.c30 Gram662ProofSharing.c42)

noncomputable def Gram662ProofSharing.c234 := (@HSub.hSub.{0, 0, 0} Complex Complex Complex (@instHSub.{0} Complex Complex.instSub) Gram662ProofSharing.c47 Gram662ProofSharing.c233)

noncomputable def Gram662ProofSharing.c235 := (Complex.log Gram662ProofSharing.c47)

noncomputable def Gram662ProofSharing.c236 := (@HMul.hMul.{0, 0, 0} Complex Complex Complex (@instHMul.{0} Complex Complex.instMul) Gram662ProofSharing.c234 Gram662ProofSharing.c235)

noncomputable def Gram662ProofSharing.c237 := (@HSub.hSub.{0, 0, 0} Complex Complex Complex (@instHSub.{0} Complex Complex.instSub) Gram662ProofSharing.c236 Gram662ProofSharing.c47)

noncomputable def Gram662ProofSharing.c238 := (@HMul.hMul.{0, 0, 0} Complex Complex Complex (@instHMul.{0} Complex Complex.instMul) Gram662ProofSharing.c233 ↑Gram662ProofSharing.c8)

noncomputable def Gram662ProofSharing.c239 := (@HAdd.hAdd.{0, 0, 0} Complex Complex Complex (@instHAdd.{0} Complex Complex.instAdd) Gram662ProofSharing.c237 Gram662ProofSharing.c238)

noncomputable def Gram662ProofSharing.c240 := (@DivInvMonoid.toZPow.{0} Complex Complex.instDivInvMonoid)

noncomputable def Gram662ProofSharing.c241 := (@ZPow.toPow.{0} Complex Gram662ProofSharing.c240)

noncomputable def Gram662ProofSharing.c242 := (@instHPow.{0, 0} Complex Int Gram662ProofSharing.c241)

noncomputable def Gram662ProofSharing.c243 := (@OfNat.ofNat.{0} Int (nat_lit 1) (@instOfNat (nat_lit 1)))

noncomputable def Gram662ProofSharing.c244 := (@OfNat.ofNat.{0} Int (nat_lit 2) (@instOfNat (nat_lit 2)))

noncomputable def Gram662ProofSharing.c245 := (nat_lit 1434036872505687715523157092921747)

noncomputable def Gram662ProofSharing.c246 := (nat_lit 16217279332302419541925553879185839630417)

noncomputable def Gram662ProofSharing.c247 := (BSN.w_sub_half_zero_mk Gram662ProofSharing.c39 Bool.false (nat_lit 101779497) (nat_lit 100000) Gram662ProofSharing.c56 (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram662ProofSharing.c248 := (Enclosure.sfrac Bool.true (nat_lit 100000) (nat_lit 400000))

noncomputable def Gram662ProofSharing.c249 := (Enclosure.Real.IsNear.const Bool.true (nat_lit 100000) (nat_lit 400000))

noncomputable def Gram662ProofSharing.c250 := (@Enclosure.Complex.IsNear.mk Gram662ProofSharing.c248 Gram662ProofSharing.c59 Bool.true (nat_lit 100000) (nat_lit 400000) (nat_lit 0) (nat_lit 1) Bool.false (nat_lit 203558994) (nat_lit 400000) (nat_lit 0) (nat_lit 1) Gram662ProofSharing.c249 Gram662ProofSharing.c61)

noncomputable def Gram662ProofSharing.c251 := (@Enclosure.Complex.IsNear.of_eq Gram662ProofSharing.c234 { re := Enclosure.sfrac Bool.true (nat_lit 100000) (nat_lit 400000), im := Enclosure.sfrac Bool.false (nat_lit 203558994) (nat_lit 400000) } Bool.true (nat_lit 100000) (nat_lit 400000) (nat_lit 0) (nat_lit 1) Bool.false (nat_lit 203558994) (nat_lit 400000) (nat_lit 0) (nat_lit 1) Gram662ProofSharing.c247 Gram662ProofSharing.c250)

noncomputable def Gram662ProofSharing.c252 := (@Enclosure.Complex.IsNear.re_isNear Gram662ProofSharing.c234 Bool.true (nat_lit 100000) (nat_lit 400000) (nat_lit 0) (nat_lit 1) Bool.false (nat_lit 203558994) (nat_lit 400000) (nat_lit 0) (nat_lit 1) Gram662ProofSharing.c251)

noncomputable def Gram662ProofSharing.c253 := (Complex.log { re := Enclosure.sfrac Bool.false (nat_lit 100000) (nat_lit 400000), im := Enclosure.sfrac Bool.false (nat_lit 203558994) (nat_lit 400000) })

noncomputable def Gram662ProofSharing.c254 := (@congrArg.{1, 1} Complex Complex Gram662ProofSharing.c47 { re := Enclosure.sfrac Bool.false (nat_lit 100000) (nat_lit 400000), im := Enclosure.sfrac Bool.false (nat_lit 203558994) (nat_lit 400000) } Complex.log Gram662ProofSharing.c57)

noncomputable def Gram662ProofSharing.c255 := (Enclosure.sfrac Bool.false (nat_lit 1) (nat_lit 2))

noncomputable def Gram662ProofSharing.c256 := (Enclosure.sfrac Bool.false (nat_lit 41436274038292036) (nat_lit 160000000000))

noncomputable def Gram662ProofSharing.c257 := (Real.log Gram662ProofSharing.c256)

noncomputable def Gram662ProofSharing.c258 := (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) Gram662ProofSharing.c255 Gram662ProofSharing.c257)

noncomputable def Gram662ProofSharing.c259 := (Enclosure.clog_re_eq (nat_lit 100000) (nat_lit 203558994) (nat_lit 400000) (nat_lit 41436274038292036) (nat_lit 160000000000) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram662ProofSharing.c260 := (Enclosure.Real.IsNear.const Bool.false (nat_lit 1) (nat_lit 2))

noncomputable def Gram662ProofSharing.c261 := (@Nat.cast.{0} Real Real.instNatCast (nat_lit 41436274038292036))

noncomputable def Gram662ProofSharing.c262 := (@Nat.cast.{0} Real Real.instNatCast (nat_lit 160000000000))

noncomputable def Gram662ProofSharing.c263 := (@HDiv.hDiv.{0, 0, 0} Real Real Real Gram662ProofSharing.c15 Gram662ProofSharing.c261 Gram662ProofSharing.c262)

noncomputable def Gram662ProofSharing.c264 := (Real.log Gram662ProofSharing.c263)

noncomputable def Gram662ProofSharing.c265 := (nat_lit 11042249462727714933346417613241433424256857396621141128477541345692266307750237110147365784491266703076368934858113985306591289860011805344768866076462798944471824933981221515065342009284448371228319144522199960507633309678274835363359090014362848795094086678169452792158120653140991122597445111637433776388376566666790234580044022326284727091200)

noncomputable def Gram662ProofSharing.c266 := (nat_lit 423473911217683480309337467548806808738731755605823470104194451689159401174143946055320103827502133186516433285098212694866013915589057747496332190508684698478574387862269944771979668696751887928140676830870936907404685938282744733422294722202775204633457313506179958618557788552709518634751005360907587560078386109633349469417134015744646840320)

noncomputable def Gram662ProofSharing.c267 := (nat_lit 108690656936067077749430723847686406952649380115487364282933298156380651086385030555369677403919239514971249669323837692203562895894432713651782737249875254093036243206972011309148846589049857796838787590422585112088676442733143414314886802927310346074275241813996158795336369224681603254283999011188022088084033862575328331727844147200)

noncomputable def Gram662ProofSharing.c268 := (BSN.artanhP (nat_lit 20464754038292036))

noncomputable def Gram662ProofSharing.c269 := (BSN.artanhQ (nat_lit 62407794038292036))

noncomputable def Gram662ProofSharing.c270 := (@BSN.binarySplit_of_base10 Gram662ProofSharing.c268 Gram662ProofSharing.c269 (nat_lit 0) (nat_lit 10) Gram662ProofSharing.c266 Gram662ProofSharing.c265 Gram662ProofSharing.c267 (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram662ProofSharing.c271 := (BSN.log_dyadic_bound (nat_lit 20464754038292036) (nat_lit 62407794038292036) (nat_lit 11) (nat_lit 10) Gram662ProofSharing.c265 (nat_lit 17179869184) (nat_lit 6600000000) Gram662ProofSharing.c266 Gram662ProofSharing.c267 (nat_lit 11699342392) (nat_lit 82872548076584072) (nat_lit 41943040000000000) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) Gram662ProofSharing.c270 (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram662ProofSharing.c272 := (BSN.log_rat_reduce_isNear (nat_lit 41436274038292036) (nat_lit 160000000000) (nat_lit 17) (nat_lit 82872548076584072) (nat_lit 41943040000000000) (nat_lit 11699342392) (nat_lit 17179869184) (nat_lit 24973259072661432) (nat_lit 36028797018963968) (nat_lit 6600000000) (nat_lit 1000000000000000) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) Gram662ProofSharing.c271 BSN.log2_near_15 (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram662ProofSharing.c273 := (@Enclosure.Real.IsNear.recentre' Gram662ProofSharing.c264 Bool.false (nat_lit 7715147739726625770938826752) (nat_lit 618970019642690137449562112) (nat_lit 1000112200000000) (nat_lit 6600000000000000000000000) (nat_lit 56135087941413991) (nat_lit 4503599627370496) (nat_lit 5000561) (nat_lit 33000000000000000) Gram662ProofSharing.c272 (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram662ProofSharing.c274 := (BSN.isNear_log_sfrac (nat_lit 41436274038292036) (nat_lit 160000000000) (nat_lit 56135087941413991) (nat_lit 4503599627370496) (nat_lit 5000561) (nat_lit 33000000000000000) Bool.false Gram662ProofSharing.c273)

noncomputable def Gram662ProofSharing.c275 := (@Enclosure.Real.IsNear.mulLit_ff Gram662ProofSharing.c255 Gram662ProofSharing.c257 (nat_lit 1) (nat_lit 2) (nat_lit 0) (nat_lit 1) (nat_lit 56135087941413991) (nat_lit 4503599627370496) (nat_lit 5000561) (nat_lit 33000000000000000) (nat_lit 56135087941413991) (nat_lit 9007199254740992) (nat_lit 5000561) (nat_lit 66000000000000000) Gram662ProofSharing.c260 Gram662ProofSharing.c274 (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram662ProofSharing.c276 := (@Enclosure.Real.IsNear.of_eq (Gram662ProofSharing.c253 : ℂ).re Gram662ProofSharing.c258 Bool.false (nat_lit 56135087941413991) (nat_lit 9007199254740992) (nat_lit 5000561) (nat_lit 66000000000000000) Gram662ProofSharing.c259 Gram662ProofSharing.c275)

noncomputable def Gram662ProofSharing.c277 := (@Nat.cast.{0} Real Real.instNatCast (nat_lit 203558994))

noncomputable def Gram662ProofSharing.c278 := (@Nat.cast.{0} Real Real.instNatCast (nat_lit 100000))

noncomputable def Gram662ProofSharing.c279 := (@HDiv.hDiv.{0, 0, 0} Real Real Real Gram662ProofSharing.c15 Gram662ProofSharing.c277 Gram662ProofSharing.c278)

noncomputable def Gram662ProofSharing.c280 := (Real.arctan Gram662ProofSharing.c279)

noncomputable def Gram662ProofSharing.c281 := (Enclosure.clog_im_eq (nat_lit 100000) (nat_lit 203558994) (nat_lit 400000) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram662ProofSharing.c282 := (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) Gram662ProofSharing.c255 Real.pi)

noncomputable def Gram662ProofSharing.c283 := (@HDiv.hDiv.{0, 0, 0} Real Real Real Gram662ProofSharing.c15 Gram662ProofSharing.c278 Gram662ProofSharing.c277)

noncomputable def Gram662ProofSharing.c284 := (Real.arctan Gram662ProofSharing.c283)

noncomputable def Gram662ProofSharing.c285 := (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) Gram662ProofSharing.c282 Gram662ProofSharing.c284)

noncomputable def Gram662ProofSharing.c286 := (BSN.arctan_recip (nat_lit 203558994) (nat_lit 100000) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram662ProofSharing.c287 := (@Enclosure.Real.IsNear.mulLit_ff Gram662ProofSharing.c255 Real.pi (nat_lit 1) (nat_lit 2) (nat_lit 0) (nat_lit 1) (nat_lit 226375608064910080) (nat_lit 72057594037927936) (nat_lit 1) (nat_lit 1000000000000000) (nat_lit 884279719003555) (nat_lit 562949953421312) (nat_lit 1) (nat_lit 2000000000000000) Gram662ProofSharing.c260 BSN.pi_near_15 (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram662ProofSharing.c288 := (@BSN.binarySplit_of_le (BSN.arctanEvenP (nat_lit 100000)) (BSN.arctanEvenQ (nat_lit 203558994)) (nat_lit 0) (nat_lit 0) (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram662ProofSharing.c289 := (@BSN.binarySplit_of_le (BSN.arctanOddP (nat_lit 100000)) (BSN.arctanOddQ (nat_lit 203558994)) (nat_lit 0) (nat_lit 0) (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram662ProofSharing.c290 := (BSN.arctan_dyadic_bound_f (nat_lit 100000) (nat_lit 203558994) (nat_lit 1) (nat_lit 0) (nat_lit 17179869184) (nat_lit 6600000000) (nat_lit 0) (nat_lit 1) (nat_lit 1) (nat_lit 0) (nat_lit 1) (nat_lit 1) (nat_lit 8439748) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) Gram662ProofSharing.c288 Gram662ProofSharing.c289 (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram662ProofSharing.c291 := (@Enclosure.Real.IsNear.subLit_ff_p Gram662ProofSharing.c282 Gram662ProofSharing.c284 (nat_lit 884279719003555) (nat_lit 562949953421312) (nat_lit 1) (nat_lit 2000000000000000) (nat_lit 8439748) (nat_lit 17179869184) (nat_lit 1) (nat_lit 6600000000) (nat_lit 15187058738801866119839744) (nat_lit 884003165341091) (nat_lit 562949953421312) (nat_lit 10000033) (nat_lit 66000000000000000) Gram662ProofSharing.c287 Gram662ProofSharing.c290 (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram662ProofSharing.c292 := (@Enclosure.Real.IsNear.of_eq Gram662ProofSharing.c280 Gram662ProofSharing.c285 Bool.false (nat_lit 884003165341091) (nat_lit 562949953421312) (nat_lit 10000033) (nat_lit 66000000000000000) Gram662ProofSharing.c286 Gram662ProofSharing.c291)

noncomputable def Gram662ProofSharing.c293 := (@Enclosure.Real.IsNear.of_eq (Gram662ProofSharing.c253 : ℂ).im Gram662ProofSharing.c280 Bool.false (nat_lit 884003165341091) (nat_lit 562949953421312) (nat_lit 10000033) (nat_lit 66000000000000000) Gram662ProofSharing.c281 Gram662ProofSharing.c292)

noncomputable def Gram662ProofSharing.c294 := (@Enclosure.Complex.IsNear.of_parts Gram662ProofSharing.c253 Bool.false (nat_lit 56135087941413991) (nat_lit 9007199254740992) (nat_lit 5000561) (nat_lit 66000000000000000) Bool.false (nat_lit 884003165341091) (nat_lit 562949953421312) (nat_lit 10000033) (nat_lit 66000000000000000) Gram662ProofSharing.c276 Gram662ProofSharing.c293)

noncomputable def Gram662ProofSharing.c295 := (@Enclosure.Complex.IsNear.of_eq Gram662ProofSharing.c235 Gram662ProofSharing.c253 Bool.false (nat_lit 56135087941413991) (nat_lit 9007199254740992) (nat_lit 5000561) (nat_lit 66000000000000000) Bool.false (nat_lit 884003165341091) (nat_lit 562949953421312) (nat_lit 10000033) (nat_lit 66000000000000000) Gram662ProofSharing.c254 Gram662ProofSharing.c294)

noncomputable def Gram662ProofSharing.c296 := (@Enclosure.Complex.IsNear.re_isNear Gram662ProofSharing.c235 Bool.false (nat_lit 56135087941413991) (nat_lit 9007199254740992) (nat_lit 5000561) (nat_lit 66000000000000000) Bool.false (nat_lit 884003165341091) (nat_lit 562949953421312) (nat_lit 10000033) (nat_lit 66000000000000000) Gram662ProofSharing.c295)

noncomputable def Gram662ProofSharing.c297 := (@Enclosure.Complex.IsNear.im_isNear Gram662ProofSharing.c234 Bool.true (nat_lit 100000) (nat_lit 400000) (nat_lit 0) (nat_lit 1) Bool.false (nat_lit 203558994) (nat_lit 400000) (nat_lit 0) (nat_lit 1) Gram662ProofSharing.c251)

noncomputable def Gram662ProofSharing.c298 := (@Enclosure.Complex.IsNear.im_isNear Gram662ProofSharing.c235 Bool.false (nat_lit 56135087941413991) (nat_lit 9007199254740992) (nat_lit 5000561) (nat_lit 66000000000000000) Bool.false (nat_lit 884003165341091) (nat_lit 562949953421312) (nat_lit 10000033) (nat_lit 66000000000000000) Gram662ProofSharing.c295)

noncomputable def Gram662ProofSharing.c299 := (↑Gram662ProofSharing.c8)

noncomputable def Gram662ProofSharing.c300 := (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) (Gram662ProofSharing.c233 : ℂ).re (Gram662ProofSharing.c299 : ℂ).re)

noncomputable def Gram662ProofSharing.c301 := (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) (Gram662ProofSharing.c233 : ℂ).im (Gram662ProofSharing.c299 : ℂ).im)

noncomputable def Gram662ProofSharing.c302 := (Enclosure.sfrac Bool.false (nat_lit 0) (nat_lit 1))

noncomputable def Gram662ProofSharing.c303 := (Enclosure.Real.IsNear.const Bool.false (nat_lit 0) (nat_lit 1))

noncomputable def Gram662ProofSharing.c304 := (@Enclosure.Complex.IsNear.mk Gram662ProofSharing.c255 Gram662ProofSharing.c302 Bool.false (nat_lit 1) (nat_lit 2) (nat_lit 0) (nat_lit 1) Bool.false (nat_lit 0) (nat_lit 1) (nat_lit 0) (nat_lit 1) Gram662ProofSharing.c260 Gram662ProofSharing.c303)

noncomputable def Gram662ProofSharing.c305 := (@Enclosure.Complex.IsNear.of_eq Gram662ProofSharing.c233 { re := Enclosure.sfrac Bool.false (nat_lit 1) (nat_lit 2), im := Enclosure.sfrac Bool.false (nat_lit 0) (nat_lit 1) } Bool.false (nat_lit 1) (nat_lit 2) (nat_lit 0) (nat_lit 1) Bool.false (nat_lit 0) (nat_lit 1) (nat_lit 0) (nat_lit 1) BSN.half_c_mk Gram662ProofSharing.c304)

noncomputable def Gram662ProofSharing.c306 := (@Enclosure.Complex.IsNear.re_isNear Gram662ProofSharing.c233 Bool.false (nat_lit 1) (nat_lit 2) (nat_lit 0) (nat_lit 1) Bool.false (nat_lit 0) (nat_lit 1) (nat_lit 0) (nat_lit 1) Gram662ProofSharing.c305)

noncomputable def Gram662ProofSharing.c307 := (Complex.ofReal_re Gram662ProofSharing.c8)

noncomputable def Gram662ProofSharing.c308 := (@Enclosure.Real.IsNear.of_eq (Gram662ProofSharing.c299 : ℂ).re Gram662ProofSharing.c8 Bool.false (nat_lit 3946810947) (nat_lit 2147483648) (nat_lit 1) (nat_lit 4294967296) Gram662ProofSharing.c307 Zeta.Certificates.Gram.gp8_cert._proof_1)

noncomputable def Gram662ProofSharing.c309 := (@Enclosure.Real.IsNear.mulLit_ff (Gram662ProofSharing.c233 : ℂ).re (Gram662ProofSharing.c299 : ℂ).re (nat_lit 1) (nat_lit 2) (nat_lit 0) (nat_lit 1) (nat_lit 3946810947) (nat_lit 2147483648) (nat_lit 1) (nat_lit 4294967296) (nat_lit 3946810947) (nat_lit 4294967296) (nat_lit 1) (nat_lit 8589934592) Gram662ProofSharing.c306 Gram662ProofSharing.c308 (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram662ProofSharing.c310 := (@Enclosure.Complex.IsNear.im_isNear Gram662ProofSharing.c233 Bool.false (nat_lit 1) (nat_lit 2) (nat_lit 0) (nat_lit 1) Bool.false (nat_lit 0) (nat_lit 1) (nat_lit 0) (nat_lit 1) Gram662ProofSharing.c305)

noncomputable def Gram662ProofSharing.c311 := (Complex.ofReal_im Gram662ProofSharing.c8)

noncomputable def Gram662ProofSharing.c312 := (@Eq.trans.{1} Real (Gram662ProofSharing.c299 : ℂ).im Gram662ProofSharing.c147 Gram662ProofSharing.c302 Gram662ProofSharing.c311 Enclosure.sfrac_zero_eq)

noncomputable def Gram662ProofSharing.c313 := (@Enclosure.Real.IsNear.of_eq (Gram662ProofSharing.c299 : ℂ).im Gram662ProofSharing.c302 Bool.false (nat_lit 0) (nat_lit 1) (nat_lit 0) (nat_lit 1) Gram662ProofSharing.c312 Gram662ProofSharing.c303)

noncomputable def Gram662ProofSharing.c314 := (@Enclosure.Real.IsNear.mulLit_ff (Gram662ProofSharing.c233 : ℂ).im (Gram662ProofSharing.c299 : ℂ).im (nat_lit 0) (nat_lit 1) (nat_lit 0) (nat_lit 1) (nat_lit 0) (nat_lit 1) (nat_lit 0) (nat_lit 1) (nat_lit 0) (nat_lit 1) (nat_lit 0) (nat_lit 1) Gram662ProofSharing.c310 Gram662ProofSharing.c313 (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram662ProofSharing.c315 := (@Enclosure.Real.IsNear.subLit_ff_p Gram662ProofSharing.c300 Gram662ProofSharing.c301 (nat_lit 3946810947) (nat_lit 4294967296) (nat_lit 1) (nat_lit 8589934592) (nat_lit 0) (nat_lit 1) (nat_lit 0) (nat_lit 1) (nat_lit 3946810947) (nat_lit 3946810947) (nat_lit 4294967296) (nat_lit 1) (nat_lit 8589934592) Gram662ProofSharing.c309 Gram662ProofSharing.c314 (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram662ProofSharing.c316 := (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) (Gram662ProofSharing.c233 : ℂ).re (Gram662ProofSharing.c299 : ℂ).im)

noncomputable def Gram662ProofSharing.c317 := (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) (Gram662ProofSharing.c233 : ℂ).im (Gram662ProofSharing.c299 : ℂ).re)

noncomputable def Gram662ProofSharing.c318 := (@Enclosure.Real.IsNear.mulLit_ff (Gram662ProofSharing.c233 : ℂ).re (Gram662ProofSharing.c299 : ℂ).im (nat_lit 1) (nat_lit 2) (nat_lit 0) (nat_lit 1) (nat_lit 0) (nat_lit 1) (nat_lit 0) (nat_lit 1) (nat_lit 0) (nat_lit 1) (nat_lit 0) (nat_lit 1) Gram662ProofSharing.c306 Gram662ProofSharing.c313 (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram662ProofSharing.c319 := (@Enclosure.Real.IsNear.mulLit_ff (Gram662ProofSharing.c233 : ℂ).im (Gram662ProofSharing.c299 : ℂ).re (nat_lit 0) (nat_lit 1) (nat_lit 0) (nat_lit 1) (nat_lit 3946810947) (nat_lit 2147483648) (nat_lit 1) (nat_lit 4294967296) (nat_lit 0) (nat_lit 1) (nat_lit 0) (nat_lit 1) Gram662ProofSharing.c310 Gram662ProofSharing.c308 (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram662ProofSharing.c320 := (@Enclosure.Real.IsNear.addLit_ff Gram662ProofSharing.c316 Gram662ProofSharing.c317 (nat_lit 0) (nat_lit 1) (nat_lit 0) (nat_lit 1) (nat_lit 0) (nat_lit 1) (nat_lit 0) (nat_lit 1) (nat_lit 0) (nat_lit 0) (nat_lit 1) (nat_lit 0) (nat_lit 1) Gram662ProofSharing.c318 Gram662ProofSharing.c319 (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram662ProofSharing.c321 := (@Enclosure.Complex.IsNear.mul Gram662ProofSharing.c233 Gram662ProofSharing.c299 Bool.false (nat_lit 3946810947) (nat_lit 4294967296) (nat_lit 1) (nat_lit 8589934592) Bool.false (nat_lit 0) (nat_lit 1) (nat_lit 0) (nat_lit 1) Gram662ProofSharing.c315 Gram662ProofSharing.c320)

noncomputable def Gram662ProofSharing.c322 := (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) Gram662ProofSharing.c32 (nat_lit 2))

noncomputable def Gram662ProofSharing.c323 := (bernoulli Gram662ProofSharing.c322)

noncomputable def Gram662ProofSharing.c324 := (@Rat.cast.{0} Complex Complex.instRatCast Gram662ProofSharing.c323)

noncomputable def Gram662ProofSharing.c325 := (@Nat.cast.{0} Complex Complex.instNatCast (nat_lit 2))

noncomputable def Gram662ProofSharing.c326 := (@HMul.hMul.{0, 0, 0} Complex Complex Complex (@instHMul.{0} Complex Complex.instMul) Gram662ProofSharing.c42 Gram662ProofSharing.c325)

noncomputable def Gram662ProofSharing.c327 := (@HSub.hSub.{0, 0, 0} Complex Complex Complex (@instHSub.{0} Complex Complex.instSub) Gram662ProofSharing.c326 Gram662ProofSharing.c30)

noncomputable def Gram662ProofSharing.c328 := (@HMul.hMul.{0, 0, 0} Complex Complex Complex (@instHMul.{0} Complex Complex.instMul) Gram662ProofSharing.c326 Gram662ProofSharing.c327)

noncomputable def Gram662ProofSharing.c329 := (@HDiv.hDiv.{0, 0, 0} Complex Complex Complex Gram662ProofSharing.c28 Gram662ProofSharing.c324 Gram662ProofSharing.c328)

noncomputable def Gram662ProofSharing.c330 := (@Nat.cast.{0} Int instNatCastInt (nat_lit 2))

noncomputable def Gram662ProofSharing.c331 := (@HMul.hMul.{0, 0, 0} Int Int Int (@instHMul.{0} Int Int.instMul) Gram662ProofSharing.c244 Gram662ProofSharing.c330)

noncomputable def Gram662ProofSharing.c332 := (@HSub.hSub.{0, 0, 0} Int Int Int (@instHSub.{0} Int Int.instSub) Gram662ProofSharing.c243 Gram662ProofSharing.c331)

noncomputable def Gram662ProofSharing.c333 := (@HPow.hPow.{0, 0, 0} Complex Int Complex Gram662ProofSharing.c242 Gram662ProofSharing.c47 Gram662ProofSharing.c332)

noncomputable def Gram662ProofSharing.c334 := (@HMul.hMul.{0, 0, 0} Complex Complex Complex (@instHMul.{0} Complex Complex.instMul) Gram662ProofSharing.c329 Gram662ProofSharing.c333)

noncomputable def Gram662ProofSharing.c335 := (nat_lit 2087351332190532291901585839630417)

noncomputable def Gram662ProofSharing.c336 := (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) Gram662ProofSharing.c32 (nat_lit 1))

noncomputable def Gram662ProofSharing.c337 := (bernoulli Gram662ProofSharing.c336)

noncomputable def Gram662ProofSharing.c338 := (@Rat.cast.{0} Complex Complex.instRatCast Gram662ProofSharing.c337)

noncomputable def Gram662ProofSharing.c339 := (@Nat.cast.{0} Complex Complex.instNatCast (nat_lit 1))

noncomputable def Gram662ProofSharing.c340 := (@HMul.hMul.{0, 0, 0} Complex Complex Complex (@instHMul.{0} Complex Complex.instMul) Gram662ProofSharing.c42 Gram662ProofSharing.c339)

noncomputable def Gram662ProofSharing.c341 := (@HSub.hSub.{0, 0, 0} Complex Complex Complex (@instHSub.{0} Complex Complex.instSub) Gram662ProofSharing.c340 Gram662ProofSharing.c30)

noncomputable def Gram662ProofSharing.c342 := (@HMul.hMul.{0, 0, 0} Complex Complex Complex (@instHMul.{0} Complex Complex.instMul) Gram662ProofSharing.c340 Gram662ProofSharing.c341)

noncomputable def Gram662ProofSharing.c343 := (@HDiv.hDiv.{0, 0, 0} Complex Complex Complex Gram662ProofSharing.c28 Gram662ProofSharing.c338 Gram662ProofSharing.c342)

noncomputable def Gram662ProofSharing.c344 := (@Nat.cast.{0} Int instNatCastInt (nat_lit 1))

noncomputable def Gram662ProofSharing.c345 := (@HMul.hMul.{0, 0, 0} Int Int Int (@instHMul.{0} Int Int.instMul) Gram662ProofSharing.c244 Gram662ProofSharing.c344)

noncomputable def Gram662ProofSharing.c346 := (@HSub.hSub.{0, 0, 0} Int Int Int (@instHSub.{0} Int Int.instSub) Gram662ProofSharing.c243 Gram662ProofSharing.c345)

noncomputable def Gram662ProofSharing.c347 := (@HPow.hPow.{0, 0, 0} Complex Int Complex Gram662ProofSharing.c242 Gram662ProofSharing.c47 Gram662ProofSharing.c346)

noncomputable def Gram662ProofSharing.c348 := (@HMul.hMul.{0, 0, 0} Complex Complex Complex (@instHMul.{0} Complex Complex.instMul) Gram662ProofSharing.c343 Gram662ProofSharing.c347)

noncomputable def Gram662ProofSharing.c349 := (@Enclosure.Complex.IsNear.mk Gram662ProofSharing.c302 Gram662ProofSharing.c302 Bool.false (nat_lit 0) (nat_lit 1) (nat_lit 0) (nat_lit 1) Bool.false (nat_lit 0) (nat_lit 1) (nat_lit 0) (nat_lit 1) Gram662ProofSharing.c303 Gram662ProofSharing.c303)

noncomputable def Gram662ProofSharing.c350 := (BSN.stirling_coeff_mk (nat_lit 1) (nat_lit 1) (nat_lit 6) Bool.false BSN.bern_real_1 (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram662ProofSharing.c351 := (Enclosure.sfrac Bool.false (nat_lit 1) (nat_lit 12))

noncomputable def Gram662ProofSharing.c352 := (Enclosure.Real.IsNear.const Bool.false (nat_lit 1) (nat_lit 12))

noncomputable def Gram662ProofSharing.c353 := (@Enclosure.Complex.IsNear.mk Gram662ProofSharing.c351 Gram662ProofSharing.c302 Bool.false (nat_lit 1) (nat_lit 12) (nat_lit 0) (nat_lit 1) Bool.false (nat_lit 0) (nat_lit 1) (nat_lit 0) (nat_lit 1) Gram662ProofSharing.c352 Gram662ProofSharing.c303)

noncomputable def Gram662ProofSharing.c354 := (@Enclosure.Complex.IsNear.of_eq Gram662ProofSharing.c343 { re := Enclosure.sfrac Bool.false (nat_lit 1) (nat_lit 12), im := Enclosure.sfrac Bool.false (nat_lit 0) (nat_lit 1) } Bool.false (nat_lit 1) (nat_lit 12) (nat_lit 0) (nat_lit 1) Bool.false (nat_lit 0) (nat_lit 1) (nat_lit 0) (nat_lit 1) Gram662ProofSharing.c350 Gram662ProofSharing.c353)

noncomputable def Gram662ProofSharing.c355 := (@Enclosure.Complex.IsNear.re_isNear Gram662ProofSharing.c343 Bool.false (nat_lit 1) (nat_lit 12) (nat_lit 0) (nat_lit 1) Bool.false (nat_lit 0) (nat_lit 1) (nat_lit 0) (nat_lit 1) Gram662ProofSharing.c354)

noncomputable def Gram662ProofSharing.c356 := (@Inv.inv.{0} Complex Complex.instInv Gram662ProofSharing.c50)

noncomputable def Gram662ProofSharing.c357 := (BSN.zpow_one_sub_two_mul Gram662ProofSharing.c47 (nat_lit 1) (nat_lit 1) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram662ProofSharing.c358 := (@instMulZeroOneClassOfSemiring.{0} Complex Complex.instSemiring)

noncomputable def Gram662ProofSharing.c359 := (@instMulZeroOneClassOfSemiring.{0} Real Real.semiring)

noncomputable def Gram662ProofSharing.c360 := (@MonoidWithZeroHom.{0, 0} Complex Real Gram662ProofSharing.c358 Gram662ProofSharing.c359)

noncomputable def Gram662ProofSharing.c361 := (@MonoidWithZeroHom.funLike.{0, 0} Complex Real Gram662ProofSharing.c358 Gram662ProofSharing.c359)

noncomputable def Gram662ProofSharing.c362 := (Enclosure.Complex.inv_re_eq_mul Gram662ProofSharing.c50)

noncomputable def Gram662ProofSharing.c363 := (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) (Gram662ProofSharing.c50 : ℂ).re (Gram662ProofSharing.c50 : ℂ).re)

noncomputable def Gram662ProofSharing.c364 := (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) (Gram662ProofSharing.c50 : ℂ).im (Gram662ProofSharing.c50 : ℂ).im)

noncomputable def Gram662ProofSharing.c365 := (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd) Gram662ProofSharing.c363 Gram662ProofSharing.c364)

noncomputable def Gram662ProofSharing.c366 := (Enclosure.Complex.normSq_eq_mul_add_mul Gram662ProofSharing.c50)

noncomputable def Gram662ProofSharing.c367 := (@Enclosure.Real.IsNear.mulLit_ff (Gram662ProofSharing.c50 : ℂ).re (Gram662ProofSharing.c50 : ℂ).re (nat_lit 100000) (nat_lit 400000) (nat_lit 0) (nat_lit 1) (nat_lit 100000) (nat_lit 400000) (nat_lit 0) (nat_lit 1) (nat_lit 1) (nat_lit 16) (nat_lit 0) (nat_lit 1) Gram662ProofSharing.c65 Gram662ProofSharing.c65 (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram662ProofSharing.c368 := (@Enclosure.Real.IsNear.mulLit_ff (Gram662ProofSharing.c50 : ℂ).im (Gram662ProofSharing.c50 : ℂ).im (nat_lit 203558994) (nat_lit 400000) (nat_lit 0) (nat_lit 1) (nat_lit 203558994) (nat_lit 400000) (nat_lit 0) (nat_lit 1) (nat_lit 10359066009573009) (nat_lit 40000000000) (nat_lit 0) (nat_lit 1) Gram662ProofSharing.c68 Gram662ProofSharing.c68 (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram662ProofSharing.c369 := (@Enclosure.Real.IsNear.addLit_ff Gram662ProofSharing.c363 Gram662ProofSharing.c364 (nat_lit 1) (nat_lit 16) (nat_lit 0) (nat_lit 1) (nat_lit 10359066009573009) (nat_lit 40000000000) (nat_lit 0) (nat_lit 1) (nat_lit 165745096153168144) (nat_lit 10359068509573009) (nat_lit 40000000000) (nat_lit 0) (nat_lit 1) Gram662ProofSharing.c367 Gram662ProofSharing.c368 (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram662ProofSharing.c370 := (@Neg.neg.{0} Real Real.instNeg (Gram662ProofSharing.c50 : ℂ).im)

noncomputable def Gram662ProofSharing.c371 := (Enclosure.Complex.inv_im_eq_mul Gram662ProofSharing.c50)

noncomputable def Gram662ProofSharing.c372 := (@Enclosure.Real.IsNear.neg (Gram662ProofSharing.c50 : ℂ).im Bool.false (nat_lit 203558994) (nat_lit 400000) (nat_lit 0) (nat_lit 1) Gram662ProofSharing.c68)

noncomputable def Gram662ProofSharing.c373 := (@Enclosure.Complex.IsNear.im_isNear Gram662ProofSharing.c343 Bool.false (nat_lit 1) (nat_lit 12) (nat_lit 0) (nat_lit 1) Bool.false (nat_lit 0) (nat_lit 1) (nat_lit 0) (nat_lit 1) Gram662ProofSharing.c354)

noncomputable def Gram662ProofSharing.c374 := (nat_lit 49517601571415210995964968960000000000)

noncomputable def Gram662ProofSharing.c375 := (BSN.stirling_coeff_mk (nat_lit 2) (nat_lit 1) (nat_lit 30) Bool.true BSN.bern_real_2 (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram662ProofSharing.c376 := (Enclosure.sfrac Bool.true (nat_lit 1) (nat_lit 360))

noncomputable def Gram662ProofSharing.c377 := (Enclosure.Real.IsNear.const Bool.true (nat_lit 1) (nat_lit 360))

noncomputable def Gram662ProofSharing.c378 := (@Enclosure.Complex.IsNear.mk Gram662ProofSharing.c376 Gram662ProofSharing.c302 Bool.true (nat_lit 1) (nat_lit 360) (nat_lit 0) (nat_lit 1) Bool.false (nat_lit 0) (nat_lit 1) (nat_lit 0) (nat_lit 1) Gram662ProofSharing.c377 Gram662ProofSharing.c303)

noncomputable def Gram662ProofSharing.c379 := (@Enclosure.Complex.IsNear.of_eq Gram662ProofSharing.c329 { re := Enclosure.sfrac Bool.true (nat_lit 1) (nat_lit 360), im := Enclosure.sfrac Bool.false (nat_lit 0) (nat_lit 1) } Bool.true (nat_lit 1) (nat_lit 360) (nat_lit 0) (nat_lit 1) Bool.false (nat_lit 0) (nat_lit 1) (nat_lit 0) (nat_lit 1) Gram662ProofSharing.c375 Gram662ProofSharing.c378)

noncomputable def Gram662ProofSharing.c380 := (@Enclosure.Complex.IsNear.re_isNear Gram662ProofSharing.c329 Bool.true (nat_lit 1) (nat_lit 360) (nat_lit 0) (nat_lit 1) Bool.false (nat_lit 0) (nat_lit 1) (nat_lit 0) (nat_lit 1) Gram662ProofSharing.c379)

noncomputable def Gram662ProofSharing.c381 := (nat_lit 18786161989714790627114272556673753)

noncomputable def Gram662ProofSharing.c382 := (nat_lit 2475880078570760549798248448000000000000000)

noncomputable def Gram662ProofSharing.c383 := (@Inv.inv.{0} Complex Complex.instInv Gram662ProofSharing.c48)

noncomputable def Gram662ProofSharing.c384 := (BSN.zpow_one_sub_two_mul Gram662ProofSharing.c47 (nat_lit 2) (nat_lit 3) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram662ProofSharing.c385 := (Enclosure.Complex.inv_re_eq_mul Gram662ProofSharing.c48)

noncomputable def Gram662ProofSharing.c386 := (@Enclosure.Complex.IsNear.re_isNear Gram662ProofSharing.c48 Bool.true (nat_lit 31077195528719027) (nat_lit 160000000000) (nat_lit 0) (nat_lit 1) Bool.true (nat_lit 1054339764497910540796473) (nat_lit 8000000000000000) (nat_lit 0) (nat_lit 1) Zeta.Certificates.Gram.gp8_cert._proof_2)

noncomputable def Gram662ProofSharing.c387 := (nat_lit 1111634753481714285985556642189759770507709239729)

noncomputable def Gram662ProofSharing.c388 := (nat_lit 64000000000000000000000000000000)

noncomputable def Gram662ProofSharing.c389 := (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) (Gram662ProofSharing.c48 : ℂ).re (Gram662ProofSharing.c48 : ℂ).re)

noncomputable def Gram662ProofSharing.c390 := (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) (Gram662ProofSharing.c48 : ℂ).im (Gram662ProofSharing.c48 : ℂ).im)

noncomputable def Gram662ProofSharing.c391 := (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd) Gram662ProofSharing.c389 Gram662ProofSharing.c390)

noncomputable def Gram662ProofSharing.c392 := (Enclosure.Complex.normSq_eq_mul_add_mul Gram662ProofSharing.c48)

noncomputable def Gram662ProofSharing.c393 := (nat_lit 965792081930233884122339511826729)

noncomputable def Gram662ProofSharing.c394 := (nat_lit 1111632339001509460400846336340980203685209239729)

noncomputable def Gram662ProofSharing.c395 := (nat_lit 28457849689131885721230250040057850124997356537062400000000000000000000)

noncomputable def Gram662ProofSharing.c396 := (@Enclosure.Real.IsNear.mulLit_tt (Gram662ProofSharing.c48 : ℂ).re (Gram662ProofSharing.c48 : ℂ).re (nat_lit 31077195528719027) (nat_lit 160000000000) (nat_lit 0) (nat_lit 1) (nat_lit 31077195528719027) (nat_lit 160000000000) (nat_lit 0) (nat_lit 1) Gram662ProofSharing.c393 (nat_lit 25600000000000000000000) (nat_lit 0) (nat_lit 1) Gram662ProofSharing.c386 Gram662ProofSharing.c386 (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram662ProofSharing.c397 := (@Enclosure.Complex.IsNear.im_isNear Gram662ProofSharing.c48 Bool.true (nat_lit 31077195528719027) (nat_lit 160000000000) (nat_lit 0) (nat_lit 1) Bool.true (nat_lit 1054339764497910540796473) (nat_lit 8000000000000000) (nat_lit 0) (nat_lit 1) Zeta.Certificates.Gram.gp8_cert._proof_2)

noncomputable def Gram662ProofSharing.c398 := (@Enclosure.Real.IsNear.mulLit_tt (Gram662ProofSharing.c48 : ℂ).im (Gram662ProofSharing.c48 : ℂ).im (nat_lit 1054339764497910540796473) (nat_lit 8000000000000000) (nat_lit 0) (nat_lit 1) (nat_lit 1054339764497910540796473) (nat_lit 8000000000000000) (nat_lit 0) (nat_lit 1) Gram662ProofSharing.c394 Gram662ProofSharing.c388 (nat_lit 0) (nat_lit 1) Gram662ProofSharing.c397 Gram662ProofSharing.c397 (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram662ProofSharing.c399 := (@Enclosure.Real.IsNear.addLit_ff Gram662ProofSharing.c389 Gram662ProofSharing.c390 Gram662ProofSharing.c393 (nat_lit 25600000000000000000000) (nat_lit 0) (nat_lit 1) Gram662ProofSharing.c394 Gram662ProofSharing.c388 (nat_lit 0) (nat_lit 1) Gram662ProofSharing.c395 Gram662ProofSharing.c387 Gram662ProofSharing.c388 (nat_lit 0) (nat_lit 1) Gram662ProofSharing.c396 Gram662ProofSharing.c398 (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram662ProofSharing.c400 := (@Neg.neg.{0} Real Real.instNeg (Gram662ProofSharing.c48 : ℂ).im)

noncomputable def Gram662ProofSharing.c401 := (Enclosure.Complex.inv_im_eq_mul Gram662ProofSharing.c48)

noncomputable def Gram662ProofSharing.c402 := (@Enclosure.Real.IsNear.neg (Gram662ProofSharing.c48 : ℂ).im Bool.true (nat_lit 1054339764497910540796473) (nat_lit 8000000000000000) (nat_lit 0) (nat_lit 1) Gram662ProofSharing.c397)

noncomputable def Gram662ProofSharing.c403 := (@Enclosure.Complex.IsNear.im_isNear Gram662ProofSharing.c329 Bool.true (nat_lit 1) (nat_lit 360) (nat_lit 0) (nat_lit 1) Bool.false (nat_lit 0) (nat_lit 1) (nat_lit 0) (nat_lit 1) Gram662ProofSharing.c379)

noncomputable def Gram662ProofSharing.c404 := (BSN.logSumC Gram662ProofSharing.c39 (nat_lit 0))

noncomputable def Gram662ProofSharing.c405 := (Enclosure.sfrac Bool.false (nat_lit 98304000000000000000000000) Gram662ProofSharing.c106)

noncomputable def Gram662ProofSharing.c406 := (@Monoid.toNPow.{0} Real Real.instMonoid)

noncomputable def Gram662ProofSharing.c407 := (@NPow.toPow.{0} Real Gram662ProofSharing.c406)

noncomputable def Gram662ProofSharing.c408 := (@instHPow.{0, 0} Real Nat Gram662ProofSharing.c407)

noncomputable def Gram662ProofSharing.c409 := (@HPow.hPow.{0, 0, 0} Real Nat Real Gram662ProofSharing.c408 Gram662ProofSharing.c7 (nat_lit 4))

noncomputable def Gram662ProofSharing.c410 := (@Inv.inv.{0} Real Real.instInv Gram662ProofSharing.c409)

noncomputable def Gram662ProofSharing.c411 := (nat_lit 611446774371975769155682509262542103857872115376664175900625)

noncomputable def Gram662ProofSharing.c412 := (nat_lit 392318858461667547739736838950479151006397215279002157056)

noncomputable def Gram662ProofSharing.c413 := (nat_lit 19652562622312316682495810535216024035134795670488584765154486969712234385047)

noncomputable def Gram662ProofSharing.c414 := (nat_lit 9903520314283042199192993792000000000000000000000000000000000000000000000000000000000000)

noncomputable def Gram662ProofSharing.c415 := (@HPow.hPow.{0, 0, 0} Real Nat Real Gram662ProofSharing.c408 Gram662ProofSharing.c7 (nat_lit 3))

noncomputable def Gram662ProofSharing.c416 := (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) Gram662ProofSharing.c415 Gram662ProofSharing.c7)

noncomputable def Gram662ProofSharing.c417 := (BSN.pow_succ_r Gram662ProofSharing.c7 (nat_lit 3) (nat_lit 4) (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram662ProofSharing.c418 := (nat_lit 691463075802508163054686763366652189853178875)

noncomputable def Gram662ProofSharing.c419 := (nat_lit 2787593149816327892691964784081045188247552)

noncomputable def Gram662ProofSharing.c420 := (nat_lit 2184744797947834540264818678394244808492865883128339)

noncomputable def Gram662ProofSharing.c421 := (nat_lit 9223372036854775808000000000000000000000000000000000000000000000)

noncomputable def Gram662ProofSharing.c422 := (@HPow.hPow.{0, 0, 0} Real Nat Real Gram662ProofSharing.c408 Gram662ProofSharing.c7 (nat_lit 2))

noncomputable def Gram662ProofSharing.c423 := (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) Gram662ProofSharing.c422 Gram662ProofSharing.c7)

noncomputable def Gram662ProofSharing.c424 := (BSN.pow_succ_r Gram662ProofSharing.c7 (nat_lit 2) (nat_lit 3) (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram662ProofSharing.c425 := (nat_lit 1073741824000000000000000000000000000000)

noncomputable def Gram662ProofSharing.c426 := (@HPow.hPow.{0, 0, 0} Real Nat Real Gram662ProofSharing.c408 Gram662ProofSharing.c7 (nat_lit 1))

noncomputable def Gram662ProofSharing.c427 := (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) Gram662ProofSharing.c426 Gram662ProofSharing.c7)

noncomputable def Gram662ProofSharing.c428 := (BSN.pow_succ_r Gram662ProofSharing.c7 (nat_lit 1) (nat_lit 2) (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram662ProofSharing.c429 := (BSN.pow_one_r Gram662ProofSharing.c7)

noncomputable def Gram662ProofSharing.c430 := (@Enclosure.Real.IsNear.of_eq Gram662ProofSharing.c7 Gram662ProofSharing.c10 Bool.false (nat_lit 884279719003555) (nat_lit 140737488355328) (nat_lit 1) (nat_lit 500000000000000) BSN.two_pi_eq Gram662ProofSharing.c13)

noncomputable def Gram662ProofSharing.c431 := (@Enclosure.Real.IsNear.of_eq Gram662ProofSharing.c426 Gram662ProofSharing.c7 Bool.false (nat_lit 884279719003555) (nat_lit 140737488355328) (nat_lit 1) (nat_lit 500000000000000) Gram662ProofSharing.c429 Gram662ProofSharing.c430)

noncomputable def Gram662ProofSharing.c432 := (@Enclosure.Real.IsNear.mulLit_ff Gram662ProofSharing.c426 Gram662ProofSharing.c7 (nat_lit 884279719003555) (nat_lit 140737488355328) (nat_lit 1) (nat_lit 500000000000000) (nat_lit 884279719003555) (nat_lit 140737488355328) (nat_lit 1) (nat_lit 500000000000000) (nat_lit 781950621441006189802102638025) (nat_lit 19807040628566084398385987584) (nat_lit 26986075409044041160201671) Gram662ProofSharing.c425 Gram662ProofSharing.c431 Gram662ProofSharing.c430 (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram662ProofSharing.c433 := (@Enclosure.Real.IsNear.of_eq Gram662ProofSharing.c422 Gram662ProofSharing.c427 Bool.false (nat_lit 781950621441006189802102638025) (nat_lit 19807040628566084398385987584) (nat_lit 26986075409044041160201671) Gram662ProofSharing.c425 Gram662ProofSharing.c428 Gram662ProofSharing.c432)

noncomputable def Gram662ProofSharing.c434 := (@Enclosure.Real.IsNear.mulLit_ff Gram662ProofSharing.c422 Gram662ProofSharing.c7 (nat_lit 781950621441006189802102638025) (nat_lit 19807040628566084398385987584) (nat_lit 26986075409044041160201671) Gram662ProofSharing.c425 (nat_lit 884279719003555) (nat_lit 140737488355328) (nat_lit 1) (nat_lit 500000000000000) Gram662ProofSharing.c418 Gram662ProofSharing.c419 Gram662ProofSharing.c420 Gram662ProofSharing.c421 Gram662ProofSharing.c433 Gram662ProofSharing.c430 (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram662ProofSharing.c435 := (@Enclosure.Real.IsNear.of_eq Gram662ProofSharing.c415 Gram662ProofSharing.c423 Bool.false Gram662ProofSharing.c418 Gram662ProofSharing.c419 Gram662ProofSharing.c420 Gram662ProofSharing.c421 Gram662ProofSharing.c424 Gram662ProofSharing.c434)

noncomputable def Gram662ProofSharing.c436 := (@Enclosure.Real.IsNear.mulLit_ff Gram662ProofSharing.c415 Gram662ProofSharing.c7 Gram662ProofSharing.c418 Gram662ProofSharing.c419 Gram662ProofSharing.c420 Gram662ProofSharing.c421 (nat_lit 884279719003555) (nat_lit 140737488355328) (nat_lit 1) (nat_lit 500000000000000) Gram662ProofSharing.c411 Gram662ProofSharing.c412 Gram662ProofSharing.c413 Gram662ProofSharing.c414 Gram662ProofSharing.c435 Gram662ProofSharing.c430 (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram662ProofSharing.c437 := (@Enclosure.Real.IsNear.of_eq Gram662ProofSharing.c409 Gram662ProofSharing.c416 Bool.false Gram662ProofSharing.c411 Gram662ProofSharing.c412 Gram662ProofSharing.c413 Gram662ProofSharing.c414 Gram662ProofSharing.c417 Gram662ProofSharing.c436)

noncomputable def Gram662ProofSharing.c438 := (@Enclosure.Real.IsNear.inv_image Gram662ProofSharing.c409 Gram662ProofSharing.c411 Gram662ProofSharing.c412 Gram662ProofSharing.c413 Gram662ProofSharing.c414 (nat_lit 5511507) (nat_lit 5511508) (nat_lit 8589934592) Gram662ProofSharing.c437 (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram662ProofSharing.c439 := (@Enclosure.Real.IsNear.recentre' Gram662ProofSharing.c410 Bool.false (nat_lit 11023015) (nat_lit 17179869184) (nat_lit 1) (nat_lit 17179869184) (nat_lit 11023015) (nat_lit 17179869184) (nat_lit 1) (nat_lit 17179869184) Gram662ProofSharing.c438 (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram662ProofSharing.c440 := (nat_lit 25746839511246548177941407661921)

noncomputable def Gram662ProofSharing.c441 := (nat_lit 792281625142643375935439503360000000)

noncomputable def Gram662ProofSharing.c442 := (nat_lit 40107148352393680566859315943786228567)

noncomputable def Gram662ProofSharing.c443 := (nat_lit 255325133102609681697944371200000000000000000)

noncomputable def Gram662ProofSharing.c444 := (riemannSiegelThetaApproximant (nat_lit 2) (nat_lit 0) Gram662ProofSharing.c107)

noncomputable def Gram662ProofSharing.c445 := (nat_lit 1647735325873809231241050107311007661921)

noncomputable def Gram662ProofSharing.c446 := (nat_lit 40106979327155566639250031904612494167)

noncomputable def Gram662ProofSharing.c447 := (Complex.Stirling.logGammaStirling (nat_lit 2) Gram662ProofSharing.c112)

noncomputable def Gram662ProofSharing.c448 := (@HDiv.hDiv.{0, 0, 0} Real Real Real Gram662ProofSharing.c15 Gram662ProofSharing.c107 Gram662ProofSharing.c6)

noncomputable def Gram662ProofSharing.c449 := (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) Gram662ProofSharing.c448 (Real.log Real.pi))

noncomputable def Gram662ProofSharing.c450 := (nat_lit 2109279126856314031216990912882386861921)

noncomputable def Gram662ProofSharing.c451 := (nat_lit 9854287521074510395538031904612494167)

noncomputable def Gram662ProofSharing.c452 := (nat_lit 57045235840715750608530711928395630413)

noncomputable def Gram662ProofSharing.c453 := (nat_lit 71305346262837903834189555302400000)

noncomputable def Gram662ProofSharing.c454 := (nat_lit 14791232583691375231077683035687598257)

noncomputable def Gram662ProofSharing.c455 := (nat_lit 191493849826957261273458278400000000000000000)

noncomputable def Gram662ProofSharing.c456 := (@HSub.hSub.{0, 0, 0} Complex Complex Complex (@instHSub.{0} Complex Complex.instSub) Gram662ProofSharing.c112 Gram662ProofSharing.c233)

noncomputable def Gram662ProofSharing.c457 := (Complex.log Gram662ProofSharing.c112)

noncomputable def Gram662ProofSharing.c458 := (@HMul.hMul.{0, 0, 0} Complex Complex Complex (@instHMul.{0} Complex Complex.instMul) Gram662ProofSharing.c456 Gram662ProofSharing.c457)

noncomputable def Gram662ProofSharing.c459 := (@HSub.hSub.{0, 0, 0} Complex Complex Complex (@instHSub.{0} Complex Complex.instSub) Gram662ProofSharing.c458 Gram662ProofSharing.c112)

noncomputable def Gram662ProofSharing.c460 := (@HAdd.hAdd.{0, 0, 0} Complex Complex Complex (@instHAdd.{0} Complex Complex.instAdd) Gram662ProofSharing.c459 Gram662ProofSharing.c238)

noncomputable def Gram662ProofSharing.c461 := (nat_lit 129738230828025058595907065938079)

noncomputable def Gram662ProofSharing.c462 := (BSN.w_sub_half_zero_mk Gram662ProofSharing.c107 Bool.false (nat_lit 101779500) (nat_lit 100000) Gram662ProofSharing.c121 (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram662ProofSharing.c463 := (@Enclosure.Complex.IsNear.mk Gram662ProofSharing.c248 Gram662ProofSharing.c123 Bool.true (nat_lit 100000) (nat_lit 400000) (nat_lit 0) (nat_lit 1) Bool.false (nat_lit 203559000) (nat_lit 400000) (nat_lit 0) (nat_lit 1) Gram662ProofSharing.c249 Gram662ProofSharing.c124)

noncomputable def Gram662ProofSharing.c464 := (@Enclosure.Complex.IsNear.of_eq Gram662ProofSharing.c456 { re := Enclosure.sfrac Bool.true (nat_lit 100000) (nat_lit 400000), im := Enclosure.sfrac Bool.false (nat_lit 203559000) (nat_lit 400000) } Bool.true (nat_lit 100000) (nat_lit 400000) (nat_lit 0) (nat_lit 1) Bool.false (nat_lit 203559000) (nat_lit 400000) (nat_lit 0) (nat_lit 1) Gram662ProofSharing.c462 Gram662ProofSharing.c463)

noncomputable def Gram662ProofSharing.c465 := (@Enclosure.Complex.IsNear.re_isNear Gram662ProofSharing.c456 Bool.true (nat_lit 100000) (nat_lit 400000) (nat_lit 0) (nat_lit 1) Bool.false (nat_lit 203559000) (nat_lit 400000) (nat_lit 0) (nat_lit 1) Gram662ProofSharing.c464)

noncomputable def Gram662ProofSharing.c466 := (Complex.log { re := Enclosure.sfrac Bool.false (nat_lit 100000) (nat_lit 400000), im := Enclosure.sfrac Bool.false (nat_lit 203559000) (nat_lit 400000) })

noncomputable def Gram662ProofSharing.c467 := (@congrArg.{1, 1} Complex Complex Gram662ProofSharing.c112 { re := Enclosure.sfrac Bool.false (nat_lit 100000) (nat_lit 400000), im := Enclosure.sfrac Bool.false (nat_lit 203559000) (nat_lit 400000) } Complex.log Gram662ProofSharing.c122)

noncomputable def Gram662ProofSharing.c468 := (Enclosure.sfrac Bool.false (nat_lit 41436276481000000) (nat_lit 160000000000))

noncomputable def Gram662ProofSharing.c469 := (Real.log Gram662ProofSharing.c468)

noncomputable def Gram662ProofSharing.c470 := (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) Gram662ProofSharing.c255 Gram662ProofSharing.c469)

noncomputable def Gram662ProofSharing.c471 := (Enclosure.clog_re_eq (nat_lit 100000) (nat_lit 203559000) (nat_lit 400000) (nat_lit 41436276481000000) (nat_lit 160000000000) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram662ProofSharing.c472 := (@Nat.cast.{0} Real Real.instNatCast (nat_lit 41436276481000000))

noncomputable def Gram662ProofSharing.c473 := (@HDiv.hDiv.{0, 0, 0} Real Real Real Gram662ProofSharing.c15 Gram662ProofSharing.c472 Gram662ProofSharing.c262)

noncomputable def Gram662ProofSharing.c474 := (Real.log Gram662ProofSharing.c473)

noncomputable def Gram662ProofSharing.c475 := (nat_lit 11042258106840569226473676077946108299011153163038332739666816970570979286460487092393149557537924247786178913884210506740387775371758290613979474339040049801928442806605119846846131185589621445691847394845727788483978532030575000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)

noncomputable def Gram662ProofSharing.c476 := (nat_lit 423474315480877718705078116438789144952327248567442499686239224070318874421539369598838370937812944137379120300805618894368785457010179675733179983167100378715813971623336237966262783891615443462672698555778088505575310003320000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)

noncomputable def Gram662ProofSharing.c477 := (nat_lit 108690916406407032083605063607320851230319028987643103352499403862090831970347223664283280491192642475214716195394202274104323709165512831561310788679561969591247637296399114390227663739619911266298219884619351049075000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)

noncomputable def Gram662ProofSharing.c478 := (BSN.artanhP (nat_lit 20464756481000000))

noncomputable def Gram662ProofSharing.c479 := (BSN.artanhQ (nat_lit 62407796481000000))

noncomputable def Gram662ProofSharing.c480 := (@BSN.binarySplit_of_base10 Gram662ProofSharing.c478 Gram662ProofSharing.c479 (nat_lit 0) (nat_lit 10) Gram662ProofSharing.c476 Gram662ProofSharing.c475 Gram662ProofSharing.c477 (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram662ProofSharing.c481 := (BSN.log_dyadic_bound (nat_lit 20464756481000000) (nat_lit 62407796481000000) (nat_lit 11) (nat_lit 10) Gram662ProofSharing.c475 (nat_lit 17179869184) (nat_lit 6600000000) Gram662ProofSharing.c476 Gram662ProofSharing.c477 (nat_lit 11699343405) (nat_lit 82872552962000000) (nat_lit 41943040000000000) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) Gram662ProofSharing.c480 (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram662ProofSharing.c482 := (BSN.log_rat_reduce_isNear (nat_lit 41436276481000000) (nat_lit 160000000000) (nat_lit 17) (nat_lit 82872552962000000) (nat_lit 41943040000000000) (nat_lit 11699343405) (nat_lit 17179869184) (nat_lit 24973259072661432) (nat_lit 36028797018963968) (nat_lit 6600000000) (nat_lit 1000000000000000) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) Gram662ProofSharing.c481 BSN.log2_near_15 (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram662ProofSharing.c483 := (@Enclosure.Real.IsNear.recentre' Gram662ProofSharing.c474 Bool.false (nat_lit 7715147776223797151149326336) (nat_lit 618970019642690137449562112) (nat_lit 1000112200000000) (nat_lit 6600000000000000000000000) (nat_lit 56135088206965863) (nat_lit 4503599627370496) (nat_lit 5000561) (nat_lit 33000000000000000) Gram662ProofSharing.c482 (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram662ProofSharing.c484 := (BSN.isNear_log_sfrac (nat_lit 41436276481000000) (nat_lit 160000000000) (nat_lit 56135088206965863) (nat_lit 4503599627370496) (nat_lit 5000561) (nat_lit 33000000000000000) Bool.false Gram662ProofSharing.c483)

noncomputable def Gram662ProofSharing.c485 := (@Enclosure.Real.IsNear.mulLit_ff Gram662ProofSharing.c255 Gram662ProofSharing.c469 (nat_lit 1) (nat_lit 2) (nat_lit 0) (nat_lit 1) (nat_lit 56135088206965863) (nat_lit 4503599627370496) (nat_lit 5000561) (nat_lit 33000000000000000) (nat_lit 56135088206965863) (nat_lit 9007199254740992) (nat_lit 5000561) (nat_lit 66000000000000000) Gram662ProofSharing.c260 Gram662ProofSharing.c484 (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram662ProofSharing.c486 := (@Enclosure.Real.IsNear.of_eq (Gram662ProofSharing.c466 : ℂ).re Gram662ProofSharing.c470 Bool.false (nat_lit 56135088206965863) (nat_lit 9007199254740992) (nat_lit 5000561) (nat_lit 66000000000000000) Gram662ProofSharing.c471 Gram662ProofSharing.c485)

noncomputable def Gram662ProofSharing.c487 := (@Nat.cast.{0} Real Real.instNatCast (nat_lit 203559000))

noncomputable def Gram662ProofSharing.c488 := (@HDiv.hDiv.{0, 0, 0} Real Real Real Gram662ProofSharing.c15 Gram662ProofSharing.c487 Gram662ProofSharing.c278)

noncomputable def Gram662ProofSharing.c489 := (Real.arctan Gram662ProofSharing.c488)

noncomputable def Gram662ProofSharing.c490 := (Enclosure.clog_im_eq (nat_lit 100000) (nat_lit 203559000) (nat_lit 400000) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram662ProofSharing.c491 := (@HDiv.hDiv.{0, 0, 0} Real Real Real Gram662ProofSharing.c15 Gram662ProofSharing.c278 Gram662ProofSharing.c487)

noncomputable def Gram662ProofSharing.c492 := (Real.arctan Gram662ProofSharing.c491)

noncomputable def Gram662ProofSharing.c493 := (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) Gram662ProofSharing.c282 Gram662ProofSharing.c492)

noncomputable def Gram662ProofSharing.c494 := (BSN.arctan_recip (nat_lit 203559000) (nat_lit 100000) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram662ProofSharing.c495 := (@BSN.binarySplit_of_le (BSN.arctanEvenP (nat_lit 100000)) (BSN.arctanEvenQ (nat_lit 203559000)) (nat_lit 0) (nat_lit 0) (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram662ProofSharing.c496 := (@BSN.binarySplit_of_le (BSN.arctanOddP (nat_lit 100000)) (BSN.arctanOddQ (nat_lit 203559000)) (nat_lit 0) (nat_lit 0) (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram662ProofSharing.c497 := (BSN.arctan_dyadic_bound_f (nat_lit 100000) (nat_lit 203559000) (nat_lit 1) (nat_lit 0) (nat_lit 17179869184) (nat_lit 6600000000) (nat_lit 0) (nat_lit 1) (nat_lit 1) (nat_lit 0) (nat_lit 1) (nat_lit 1) (nat_lit 8439748) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) Gram662ProofSharing.c495 Gram662ProofSharing.c496 (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram662ProofSharing.c498 := (@Enclosure.Real.IsNear.subLit_ff_p Gram662ProofSharing.c282 Gram662ProofSharing.c492 (nat_lit 884279719003555) (nat_lit 562949953421312) (nat_lit 1) (nat_lit 2000000000000000) (nat_lit 8439748) (nat_lit 17179869184) (nat_lit 1) (nat_lit 6600000000) (nat_lit 15187058738801866119839744) (nat_lit 884003165341091) (nat_lit 562949953421312) (nat_lit 10000033) (nat_lit 66000000000000000) Gram662ProofSharing.c287 Gram662ProofSharing.c497 (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram662ProofSharing.c499 := (@Enclosure.Real.IsNear.of_eq Gram662ProofSharing.c489 Gram662ProofSharing.c493 Bool.false (nat_lit 884003165341091) (nat_lit 562949953421312) (nat_lit 10000033) (nat_lit 66000000000000000) Gram662ProofSharing.c494 Gram662ProofSharing.c498)

noncomputable def Gram662ProofSharing.c500 := (@Enclosure.Real.IsNear.of_eq (Gram662ProofSharing.c466 : ℂ).im Gram662ProofSharing.c489 Bool.false (nat_lit 884003165341091) (nat_lit 562949953421312) (nat_lit 10000033) (nat_lit 66000000000000000) Gram662ProofSharing.c490 Gram662ProofSharing.c499)

noncomputable def Gram662ProofSharing.c501 := (@Enclosure.Complex.IsNear.of_parts Gram662ProofSharing.c466 Bool.false (nat_lit 56135088206965863) (nat_lit 9007199254740992) (nat_lit 5000561) (nat_lit 66000000000000000) Bool.false (nat_lit 884003165341091) (nat_lit 562949953421312) (nat_lit 10000033) (nat_lit 66000000000000000) Gram662ProofSharing.c486 Gram662ProofSharing.c500)

noncomputable def Gram662ProofSharing.c502 := (@Enclosure.Complex.IsNear.of_eq Gram662ProofSharing.c457 Gram662ProofSharing.c466 Bool.false (nat_lit 56135088206965863) (nat_lit 9007199254740992) (nat_lit 5000561) (nat_lit 66000000000000000) Bool.false (nat_lit 884003165341091) (nat_lit 562949953421312) (nat_lit 10000033) (nat_lit 66000000000000000) Gram662ProofSharing.c467 Gram662ProofSharing.c501)

noncomputable def Gram662ProofSharing.c503 := (@Enclosure.Complex.IsNear.re_isNear Gram662ProofSharing.c457 Bool.false (nat_lit 56135088206965863) (nat_lit 9007199254740992) (nat_lit 5000561) (nat_lit 66000000000000000) Bool.false (nat_lit 884003165341091) (nat_lit 562949953421312) (nat_lit 10000033) (nat_lit 66000000000000000) Gram662ProofSharing.c502)

noncomputable def Gram662ProofSharing.c504 := (@Enclosure.Complex.IsNear.im_isNear Gram662ProofSharing.c456 Bool.true (nat_lit 100000) (nat_lit 400000) (nat_lit 0) (nat_lit 1) Bool.false (nat_lit 203559000) (nat_lit 400000) (nat_lit 0) (nat_lit 1) Gram662ProofSharing.c464)

noncomputable def Gram662ProofSharing.c505 := (@Enclosure.Complex.IsNear.im_isNear Gram662ProofSharing.c457 Bool.false (nat_lit 56135088206965863) (nat_lit 9007199254740992) (nat_lit 5000561) (nat_lit 66000000000000000) Bool.false (nat_lit 884003165341091) (nat_lit 562949953421312) (nat_lit 10000033) (nat_lit 66000000000000000) Gram662ProofSharing.c502)

noncomputable def Gram662ProofSharing.c506 := (@HPow.hPow.{0, 0, 0} Complex Int Complex Gram662ProofSharing.c242 Gram662ProofSharing.c112 Gram662ProofSharing.c332)

noncomputable def Gram662ProofSharing.c507 := (@HMul.hMul.{0, 0, 0} Complex Complex Complex (@instHMul.{0} Complex Complex.instMul) Gram662ProofSharing.c329 Gram662ProofSharing.c506)

noncomputable def Gram662ProofSharing.c508 := (@HPow.hPow.{0, 0, 0} Complex Int Complex Gram662ProofSharing.c242 Gram662ProofSharing.c112 Gram662ProofSharing.c346)

noncomputable def Gram662ProofSharing.c509 := (@HMul.hMul.{0, 0, 0} Complex Complex Complex (@instHMul.{0} Complex Complex.instMul) Gram662ProofSharing.c343 Gram662ProofSharing.c508)

noncomputable def Gram662ProofSharing.c510 := (@Inv.inv.{0} Complex Complex.instInv Gram662ProofSharing.c115)

noncomputable def Gram662ProofSharing.c511 := (BSN.zpow_one_sub_two_mul Gram662ProofSharing.c112 (nat_lit 1) (nat_lit 1) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram662ProofSharing.c512 := (Enclosure.Complex.inv_re_eq_mul Gram662ProofSharing.c115)

noncomputable def Gram662ProofSharing.c513 := (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) (Gram662ProofSharing.c115 : ℂ).re (Gram662ProofSharing.c115 : ℂ).re)

noncomputable def Gram662ProofSharing.c514 := (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) (Gram662ProofSharing.c115 : ℂ).im (Gram662ProofSharing.c115 : ℂ).im)

noncomputable def Gram662ProofSharing.c515 := (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd) Gram662ProofSharing.c513 Gram662ProofSharing.c514)

noncomputable def Gram662ProofSharing.c516 := (Enclosure.Complex.normSq_eq_mul_add_mul Gram662ProofSharing.c115)

noncomputable def Gram662ProofSharing.c517 := (@Enclosure.Real.IsNear.mulLit_ff (Gram662ProofSharing.c115 : ℂ).re (Gram662ProofSharing.c115 : ℂ).re (nat_lit 100000) (nat_lit 400000) (nat_lit 0) (nat_lit 1) (nat_lit 100000) (nat_lit 400000) (nat_lit 0) (nat_lit 1) (nat_lit 1) (nat_lit 16) (nat_lit 0) (nat_lit 1) Gram662ProofSharing.c128 Gram662ProofSharing.c128 (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram662ProofSharing.c518 := (@Enclosure.Real.IsNear.mulLit_ff (Gram662ProofSharing.c115 : ℂ).im (Gram662ProofSharing.c115 : ℂ).im (nat_lit 203559000) (nat_lit 400000) (nat_lit 0) (nat_lit 1) (nat_lit 203559000) (nat_lit 400000) (nat_lit 0) (nat_lit 1) (nat_lit 41436266481) (nat_lit 160000) (nat_lit 0) (nat_lit 1) Gram662ProofSharing.c131 Gram662ProofSharing.c131 (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram662ProofSharing.c519 := (@Enclosure.Real.IsNear.addLit_ff Gram662ProofSharing.c513 Gram662ProofSharing.c514 (nat_lit 1) (nat_lit 16) (nat_lit 0) (nat_lit 1) (nat_lit 41436266481) (nat_lit 160000) (nat_lit 0) (nat_lit 1) (nat_lit 662980423696) (nat_lit 41436276481) (nat_lit 160000) (nat_lit 0) (nat_lit 1) Gram662ProofSharing.c517 Gram662ProofSharing.c518 (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram662ProofSharing.c520 := (@Neg.neg.{0} Real Real.instNeg (Gram662ProofSharing.c115 : ℂ).im)

noncomputable def Gram662ProofSharing.c521 := (Enclosure.Complex.inv_im_eq_mul Gram662ProofSharing.c115)

noncomputable def Gram662ProofSharing.c522 := (@Enclosure.Real.IsNear.neg (Gram662ProofSharing.c115 : ℂ).im Bool.false (nat_lit 203559000) (nat_lit 400000) (nat_lit 0) (nat_lit 1) Gram662ProofSharing.c131)

noncomputable def Gram662ProofSharing.c523 := (nat_lit 198070406285660843983859875840000)

noncomputable def Gram662ProofSharing.c524 := (nat_lit 19807040628566084398385987584000000)

noncomputable def Gram662ProofSharing.c525 := (@Inv.inv.{0} Complex Complex.instInv Gram662ProofSharing.c113)

noncomputable def Gram662ProofSharing.c526 := (BSN.zpow_one_sub_two_mul Gram662ProofSharing.c112 (nat_lit 2) (nat_lit 3) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram662ProofSharing.c527 := (Enclosure.Complex.inv_re_eq_mul Gram662ProofSharing.c113)

noncomputable def Gram662ProofSharing.c528 := (@Enclosure.Complex.IsNear.re_isNear Gram662ProofSharing.c113 Bool.true (nat_lit 124308789443) (nat_lit 640000) (nat_lit 0) (nat_lit 1) Bool.true (nat_lit 8434718861835879) (nat_lit 64000000) (nat_lit 0) (nat_lit 1) Zeta.Certificates.Gram.gp8_cert._proof_6)

noncomputable def Gram662ProofSharing.c529 := (nat_lit 71144636804961273896408834192641)

noncomputable def Gram662ProofSharing.c530 := (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) (Gram662ProofSharing.c113 : ℂ).re (Gram662ProofSharing.c113 : ℂ).re)

noncomputable def Gram662ProofSharing.c531 := (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) (Gram662ProofSharing.c113 : ℂ).im (Gram662ProofSharing.c113 : ℂ).im)

noncomputable def Gram662ProofSharing.c532 := (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd) Gram662ProofSharing.c530 Gram662ProofSharing.c531)

noncomputable def Gram662ProofSharing.c533 := (Enclosure.Complex.normSq_eq_mul_add_mul Gram662ProofSharing.c113)

noncomputable def Gram662ProofSharing.c534 := (nat_lit 71144482278209946055326331702641)

noncomputable def Gram662ProofSharing.c535 := (nat_lit 29140843235312137787969058485305753600000000)

noncomputable def Gram662ProofSharing.c536 := (@Enclosure.Real.IsNear.mulLit_tt (Gram662ProofSharing.c113 : ℂ).re (Gram662ProofSharing.c113 : ℂ).re (nat_lit 124308789443) (nat_lit 640000) (nat_lit 0) (nat_lit 1) (nat_lit 124308789443) (nat_lit 640000) (nat_lit 0) (nat_lit 1) (nat_lit 15452675132784108250249) (nat_lit 409600000000) (nat_lit 0) (nat_lit 1) Gram662ProofSharing.c528 Gram662ProofSharing.c528 (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram662ProofSharing.c537 := (@Enclosure.Complex.IsNear.im_isNear Gram662ProofSharing.c113 Bool.true (nat_lit 124308789443) (nat_lit 640000) (nat_lit 0) (nat_lit 1) Bool.true (nat_lit 8434718861835879) (nat_lit 64000000) (nat_lit 0) (nat_lit 1) Zeta.Certificates.Gram.gp8_cert._proof_6)

noncomputable def Gram662ProofSharing.c538 := (@Enclosure.Real.IsNear.mulLit_tt (Gram662ProofSharing.c113 : ℂ).im (Gram662ProofSharing.c113 : ℂ).im (nat_lit 8434718861835879) (nat_lit 64000000) (nat_lit 0) (nat_lit 1) (nat_lit 8434718861835879) (nat_lit 64000000) (nat_lit 0) (nat_lit 1) Gram662ProofSharing.c534 (nat_lit 4096000000000000) (nat_lit 0) (nat_lit 1) Gram662ProofSharing.c537 Gram662ProofSharing.c537 (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram662ProofSharing.c539 := (@Enclosure.Real.IsNear.addLit_ff Gram662ProofSharing.c530 Gram662ProofSharing.c531 (nat_lit 15452675132784108250249) (nat_lit 409600000000) (nat_lit 0) (nat_lit 1) Gram662ProofSharing.c534 (nat_lit 4096000000000000) (nat_lit 0) (nat_lit 1) Gram662ProofSharing.c535 Gram662ProofSharing.c529 (nat_lit 4096000000000000) (nat_lit 0) (nat_lit 1) Gram662ProofSharing.c536 Gram662ProofSharing.c538 (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram662ProofSharing.c540 := (@Neg.neg.{0} Real Real.instNeg (Gram662ProofSharing.c113 : ℂ).im)

noncomputable def Gram662ProofSharing.c541 := (Enclosure.Complex.inv_im_eq_mul Gram662ProofSharing.c113)

noncomputable def Gram662ProofSharing.c542 := (@Enclosure.Real.IsNear.neg (Gram662ProofSharing.c113 : ℂ).im Bool.true (nat_lit 8434718861835879) (nat_lit 64000000) (nat_lit 0) (nat_lit 1) Gram662ProofSharing.c537)

noncomputable def Gram662ProofSharing.c543 := (BSN.logSumC Gram662ProofSharing.c107 (nat_lit 0))

noncomputable def Gram662ProofSharing.c544 := (Enclosure.sfrac Bool.false (nat_lit 98304000000000000000000000) Gram662ProofSharing.c144)


