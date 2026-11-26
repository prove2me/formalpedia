-- Prove2me | Definitions.Def_RHGram660_20261117_Shared_P02_v1
-- name    : RHGram660_20261117_Shared_P02_v1
-- status  : Definition
-- author  : @bueno_ricardo
-- created : 2026-11-17T23:14:46.397229+00:00
-- url     : https://prove2.me/theorems/75f9b8fd-76c3-4cf8-95b1-051552c5a41f
-- title:
--   Gram 660 ordinary shared terms, part 2
-- statement:
--   Exact shared expressions and complete ordinary auxiliary proofs for the endpoint certificate of Gram point 660. No additional axioms or custom proof generators. Imports the already published analytic and numerical support modules.
-- source:
--   Salvatore Mercuri and Bhavik Mehta, smmercuri/zeta commit 3dab6480a82f1bfc5de0a59550e279cf50490033; Apache-2.0. Ordinary proof export and exact sharing by Desenvolvimento RH. Full expanded strict AXLE and cumulative prefixes: c75db991-1cf7-4768-a86d-129fc6d0bf49, 0b0a34ef-fc0c-4680-8def-4750a86e77ff, 9a34475f-42ce-46ae-b122-c777218b8f7d.

import Definitions.Def_RHGram660_20261117_Shared_P01_v1
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
noncomputable def Gram660ProofSharing.c224 := (Complex.Stirling.logGammaStirling (nat_lit 2) Gram660ProofSharing.c47)

noncomputable def Gram660ProofSharing.c225 := (@HDiv.hDiv.{0, 0, 0} Real Real Real Gram660ProofSharing.c15 Gram660ProofSharing.c39 Gram660ProofSharing.c6)

noncomputable def Gram660ProofSharing.c226 := (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) Gram660ProofSharing.c225 (Real.log Real.pi))

noncomputable def Gram660ProofSharing.c227 := (nat_lit 295759776607293055455980511013075944036671930473)

noncomputable def Gram660ProofSharing.c228 := (nat_lit 29491170230767655027806235933019592128227)

noncomputable def Gram660ProofSharing.c229 := (nat_lit 3556676745374610672991399242656418710028707)

noncomputable def Gram660ProofSharing.c230 := (nat_lit 4456584141427368989636847206400000000000)

noncomputable def Gram660ProofSharing.c231 := (nat_lit 670699560428475341794999274270096432287)

noncomputable def Gram660ProofSharing.c232 := (nat_lit 8704265901225330057884467200000000000000000000)

noncomputable def Gram660ProofSharing.c233 := (@HDiv.hDiv.{0, 0, 0} Complex Complex Complex Gram660ProofSharing.c28 Gram660ProofSharing.c30 Gram660ProofSharing.c42)

noncomputable def Gram660ProofSharing.c234 := (@HSub.hSub.{0, 0, 0} Complex Complex Complex (@instHSub.{0} Complex Complex.instSub) Gram660ProofSharing.c47 Gram660ProofSharing.c233)

noncomputable def Gram660ProofSharing.c235 := (Complex.log Gram660ProofSharing.c47)

noncomputable def Gram660ProofSharing.c236 := (@HMul.hMul.{0, 0, 0} Complex Complex Complex (@instHMul.{0} Complex Complex.instMul) Gram660ProofSharing.c234 Gram660ProofSharing.c235)

noncomputable def Gram660ProofSharing.c237 := (@HSub.hSub.{0, 0, 0} Complex Complex Complex (@instHSub.{0} Complex Complex.instSub) Gram660ProofSharing.c236 Gram660ProofSharing.c47)

noncomputable def Gram660ProofSharing.c238 := (@HMul.hMul.{0, 0, 0} Complex Complex Complex (@instHMul.{0} Complex Complex.instMul) Gram660ProofSharing.c233 ↑Gram660ProofSharing.c8)

noncomputable def Gram660ProofSharing.c239 := (@HAdd.hAdd.{0, 0, 0} Complex Complex Complex (@instHAdd.{0} Complex Complex.instAdd) Gram660ProofSharing.c237 Gram660ProofSharing.c238)

noncomputable def Gram660ProofSharing.c240 := (@DivInvMonoid.toZPow.{0} Complex Complex.instDivInvMonoid)

noncomputable def Gram660ProofSharing.c241 := (@ZPow.toPow.{0} Complex Gram660ProofSharing.c240)

noncomputable def Gram660ProofSharing.c242 := (@instHPow.{0, 0} Complex Int Gram660ProofSharing.c241)

noncomputable def Gram660ProofSharing.c243 := (@OfNat.ofNat.{0} Int (nat_lit 1) (@instOfNat (nat_lit 1)))

noncomputable def Gram660ProofSharing.c244 := (@OfNat.ofNat.{0} Int (nat_lit 2) (@instOfNat (nat_lit 2)))

noncomputable def Gram660ProofSharing.c245 := (nat_lit 360256091268565376354448489971293)

noncomputable def Gram660ProofSharing.c246 := (nat_lit 18288834173998398579935786827163328069527)

noncomputable def Gram660ProofSharing.c247 := (nat_lit 1046588491266913737788851740313)

noncomputable def Gram660ProofSharing.c248 := (BSN.w_sub_half_zero_mk Gram660ProofSharing.c39 Bool.false (nat_lit 101532434) (nat_lit 100000) Gram660ProofSharing.c56 (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram660ProofSharing.c249 := (Enclosure.sfrac Bool.true (nat_lit 100000) (nat_lit 400000))

noncomputable def Gram660ProofSharing.c250 := (Enclosure.Real.IsNear.const Bool.true (nat_lit 100000) (nat_lit 400000))

noncomputable def Gram660ProofSharing.c251 := (@Enclosure.Complex.IsNear.mk Gram660ProofSharing.c249 Gram660ProofSharing.c59 Bool.true (nat_lit 100000) (nat_lit 400000) (nat_lit 0) (nat_lit 1) Bool.false (nat_lit 203064868) (nat_lit 400000) (nat_lit 0) (nat_lit 1) Gram660ProofSharing.c250 Gram660ProofSharing.c61)

noncomputable def Gram660ProofSharing.c252 := (@Enclosure.Complex.IsNear.of_eq Gram660ProofSharing.c234 { re := Enclosure.sfrac Bool.true (nat_lit 100000) (nat_lit 400000), im := Enclosure.sfrac Bool.false (nat_lit 203064868) (nat_lit 400000) } Bool.true (nat_lit 100000) (nat_lit 400000) (nat_lit 0) (nat_lit 1) Bool.false (nat_lit 203064868) (nat_lit 400000) (nat_lit 0) (nat_lit 1) Gram660ProofSharing.c248 Gram660ProofSharing.c251)

noncomputable def Gram660ProofSharing.c253 := (@Enclosure.Complex.IsNear.re_isNear Gram660ProofSharing.c234 Bool.true (nat_lit 100000) (nat_lit 400000) (nat_lit 0) (nat_lit 1) Bool.false (nat_lit 203064868) (nat_lit 400000) (nat_lit 0) (nat_lit 1) Gram660ProofSharing.c252)

noncomputable def Gram660ProofSharing.c254 := (Complex.log { re := Enclosure.sfrac Bool.false (nat_lit 100000) (nat_lit 400000), im := Enclosure.sfrac Bool.false (nat_lit 203064868) (nat_lit 400000) })

noncomputable def Gram660ProofSharing.c255 := (@congrArg.{1, 1} Complex Complex Gram660ProofSharing.c47 { re := Enclosure.sfrac Bool.false (nat_lit 100000) (nat_lit 400000), im := Enclosure.sfrac Bool.false (nat_lit 203064868) (nat_lit 400000) } Complex.log Gram660ProofSharing.c57)

noncomputable def Gram660ProofSharing.c256 := (Enclosure.sfrac Bool.false (nat_lit 1) (nat_lit 2))

noncomputable def Gram660ProofSharing.c257 := (Enclosure.sfrac Bool.false (nat_lit 41235350615857424) (nat_lit 160000000000))

noncomputable def Gram660ProofSharing.c258 := (Real.log Gram660ProofSharing.c257)

noncomputable def Gram660ProofSharing.c259 := (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) Gram660ProofSharing.c256 Gram660ProofSharing.c258)

noncomputable def Gram660ProofSharing.c260 := (Enclosure.clog_re_eq (nat_lit 100000) (nat_lit 203064868) (nat_lit 400000) (nat_lit 41235350615857424) (nat_lit 160000000000) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram660ProofSharing.c261 := (Enclosure.Real.IsNear.const Bool.false (nat_lit 1) (nat_lit 2))

noncomputable def Gram660ProofSharing.c262 := (@Nat.cast.{0} Real Real.instNatCast (nat_lit 41235350615857424))

noncomputable def Gram660ProofSharing.c263 := (@Nat.cast.{0} Real Real.instNatCast (nat_lit 160000000000))

noncomputable def Gram660ProofSharing.c264 := (@HDiv.hDiv.{0, 0, 0} Real Real Real Gram660ProofSharing.c15 Gram660ProofSharing.c262 Gram660ProofSharing.c263)

noncomputable def Gram660ProofSharing.c265 := (Real.log Gram660ProofSharing.c264)

noncomputable def Gram660ProofSharing.c266 := (nat_lit 10352565974312000709906141900072971985717651371900884180445632782653313825465080096043420733049792151120952350836260827204805531908071388355822784340338486464456443959671015158476331283148917262517911949684713630828708661874166371604638051781792782197526053776257095689899729441058948353551940398405633996486041338595893597231772675107676435251200)

noncomputable def Gram660ProofSharing.c267 := (nat_lit 391419228942362124531867914444969543158129369827030783672115043476123951569026706585589055309917985837410519976703013281285538277455688874585708032328577647696824648955931291414649590621960253314094142556090634677481681393139695027209310617936500906767117640376719039969742759291694029724742920888159160944705716034245745312544047502324997816320)

noncomputable def Gram660ProofSharing.c268 := (nat_lit 89226233078986204194234720962361657882730416230058251859788267899825541317943969072919296818309467343737941263123237878561339713773832592881416824865641170118148053646427284764349032353645391368858773816592434843104963773106667062611331774242808839684463685079718498586385702741098672209069594402317151319616246677558030288936973107200)

noncomputable def Gram660ProofSharing.c269 := (BSN.artanhP (nat_lit 20263830615857424))

noncomputable def Gram660ProofSharing.c270 := (BSN.artanhQ (nat_lit 62206870615857424))

noncomputable def Gram660ProofSharing.c271 := (@BSN.binarySplit_of_base10 Gram660ProofSharing.c269 Gram660ProofSharing.c270 (nat_lit 0) (nat_lit 10) Gram660ProofSharing.c267 Gram660ProofSharing.c266 Gram660ProofSharing.c268 (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram660ProofSharing.c272 := (BSN.log_dyadic_bound (nat_lit 20263830615857424) (nat_lit 62206870615857424) (nat_lit 11) (nat_lit 10) Gram660ProofSharing.c266 (nat_lit 17179869184) (nat_lit 6600000000) Gram660ProofSharing.c267 Gram660ProofSharing.c268 (nat_lit 11615835024) (nat_lit 82470701231714848) (nat_lit 41943040000000000) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) Gram660ProofSharing.c271 (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram660ProofSharing.c273 := (BSN.log_rat_reduce_isNear (nat_lit 41235350615857424) (nat_lit 160000000000) (nat_lit 17) (nat_lit 82470701231714848) (nat_lit 41943040000000000) (nat_lit 11615835024) (nat_lit 17179869184) (nat_lit 24973259072661432) (nat_lit 36028797018963968) (nat_lit 6600000000) (nat_lit 1000000000000000) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) Gram660ProofSharing.c272 BSN.log2_near_15 (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram660ProofSharing.c274 := (@Enclosure.Real.IsNear.recentre' Gram660ProofSharing.c265 Bool.false (nat_lit 7712139069715365843884310528) (nat_lit 618970019642690137449562112) (nat_lit 1000112200000000) (nat_lit 6600000000000000000000000) (nat_lit 56113196985936999) (nat_lit 4503599627370496) (nat_lit 5000561) (nat_lit 33000000000000000) Gram660ProofSharing.c273 (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram660ProofSharing.c275 := (BSN.isNear_log_sfrac (nat_lit 41235350615857424) (nat_lit 160000000000) (nat_lit 56113196985936999) (nat_lit 4503599627370496) (nat_lit 5000561) (nat_lit 33000000000000000) Bool.false Gram660ProofSharing.c274)

noncomputable def Gram660ProofSharing.c276 := (@Enclosure.Real.IsNear.mulLit_ff Gram660ProofSharing.c256 Gram660ProofSharing.c258 (nat_lit 1) (nat_lit 2) (nat_lit 0) (nat_lit 1) (nat_lit 56113196985936999) (nat_lit 4503599627370496) (nat_lit 5000561) (nat_lit 33000000000000000) (nat_lit 56113196985936999) (nat_lit 9007199254740992) (nat_lit 5000561) (nat_lit 66000000000000000) Gram660ProofSharing.c261 Gram660ProofSharing.c275 (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram660ProofSharing.c277 := (@Enclosure.Real.IsNear.of_eq (Gram660ProofSharing.c254 : ℂ).re Gram660ProofSharing.c259 Bool.false (nat_lit 56113196985936999) (nat_lit 9007199254740992) (nat_lit 5000561) (nat_lit 66000000000000000) Gram660ProofSharing.c260 Gram660ProofSharing.c276)

noncomputable def Gram660ProofSharing.c278 := (@Nat.cast.{0} Real Real.instNatCast (nat_lit 203064868))

noncomputable def Gram660ProofSharing.c279 := (@Nat.cast.{0} Real Real.instNatCast (nat_lit 100000))

noncomputable def Gram660ProofSharing.c280 := (@HDiv.hDiv.{0, 0, 0} Real Real Real Gram660ProofSharing.c15 Gram660ProofSharing.c278 Gram660ProofSharing.c279)

noncomputable def Gram660ProofSharing.c281 := (Real.arctan Gram660ProofSharing.c280)

noncomputable def Gram660ProofSharing.c282 := (Enclosure.clog_im_eq (nat_lit 100000) (nat_lit 203064868) (nat_lit 400000) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram660ProofSharing.c283 := (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) Gram660ProofSharing.c256 Real.pi)

noncomputable def Gram660ProofSharing.c284 := (@HDiv.hDiv.{0, 0, 0} Real Real Real Gram660ProofSharing.c15 Gram660ProofSharing.c279 Gram660ProofSharing.c278)

noncomputable def Gram660ProofSharing.c285 := (Real.arctan Gram660ProofSharing.c284)

noncomputable def Gram660ProofSharing.c286 := (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) Gram660ProofSharing.c283 Gram660ProofSharing.c285)

noncomputable def Gram660ProofSharing.c287 := (BSN.arctan_recip (nat_lit 203064868) (nat_lit 100000) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram660ProofSharing.c288 := (@Enclosure.Real.IsNear.mulLit_ff Gram660ProofSharing.c256 Real.pi (nat_lit 1) (nat_lit 2) (nat_lit 0) (nat_lit 1) (nat_lit 226375608064910080) (nat_lit 72057594037927936) (nat_lit 1) (nat_lit 1000000000000000) (nat_lit 884279719003555) (nat_lit 562949953421312) (nat_lit 1) (nat_lit 2000000000000000) Gram660ProofSharing.c261 BSN.pi_near_15 (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram660ProofSharing.c289 := (@BSN.binarySplit_of_le (BSN.arctanEvenP (nat_lit 100000)) (BSN.arctanEvenQ (nat_lit 203064868)) (nat_lit 0) (nat_lit 0) (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram660ProofSharing.c290 := (@BSN.binarySplit_of_le (BSN.arctanOddP (nat_lit 100000)) (BSN.arctanOddQ (nat_lit 203064868)) (nat_lit 0) (nat_lit 0) (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram660ProofSharing.c291 := (BSN.arctan_dyadic_bound_f (nat_lit 100000) (nat_lit 203064868) (nat_lit 1) (nat_lit 0) (nat_lit 17179869184) (nat_lit 6600000000) (nat_lit 0) (nat_lit 1) (nat_lit 1) (nat_lit 0) (nat_lit 1) (nat_lit 1) (nat_lit 8460285) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) Gram660ProofSharing.c289 Gram660ProofSharing.c290 (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram660ProofSharing.c292 := (@Enclosure.Real.IsNear.subLit_ff_p Gram660ProofSharing.c283 Gram660ProofSharing.c285 (nat_lit 884279719003555) (nat_lit 562949953421312) (nat_lit 1) (nat_lit 2000000000000000) (nat_lit 8460285) (nat_lit 17179869184) (nat_lit 1) (nat_lit 6600000000) (nat_lit 15187047177498672706355200) (nat_lit 884002492384675) (nat_lit 562949953421312) (nat_lit 10000033) (nat_lit 66000000000000000) Gram660ProofSharing.c288 Gram660ProofSharing.c291 (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram660ProofSharing.c293 := (@Enclosure.Real.IsNear.of_eq Gram660ProofSharing.c281 Gram660ProofSharing.c286 Bool.false (nat_lit 884002492384675) (nat_lit 562949953421312) (nat_lit 10000033) (nat_lit 66000000000000000) Gram660ProofSharing.c287 Gram660ProofSharing.c292)

noncomputable def Gram660ProofSharing.c294 := (@Enclosure.Real.IsNear.of_eq (Gram660ProofSharing.c254 : ℂ).im Gram660ProofSharing.c281 Bool.false (nat_lit 884002492384675) (nat_lit 562949953421312) (nat_lit 10000033) (nat_lit 66000000000000000) Gram660ProofSharing.c282 Gram660ProofSharing.c293)

noncomputable def Gram660ProofSharing.c295 := (@Enclosure.Complex.IsNear.of_parts Gram660ProofSharing.c254 Bool.false (nat_lit 56113196985936999) (nat_lit 9007199254740992) (nat_lit 5000561) (nat_lit 66000000000000000) Bool.false (nat_lit 884002492384675) (nat_lit 562949953421312) (nat_lit 10000033) (nat_lit 66000000000000000) Gram660ProofSharing.c277 Gram660ProofSharing.c294)

noncomputable def Gram660ProofSharing.c296 := (@Enclosure.Complex.IsNear.of_eq Gram660ProofSharing.c235 Gram660ProofSharing.c254 Bool.false (nat_lit 56113196985936999) (nat_lit 9007199254740992) (nat_lit 5000561) (nat_lit 66000000000000000) Bool.false (nat_lit 884002492384675) (nat_lit 562949953421312) (nat_lit 10000033) (nat_lit 66000000000000000) Gram660ProofSharing.c255 Gram660ProofSharing.c295)

noncomputable def Gram660ProofSharing.c297 := (@Enclosure.Complex.IsNear.re_isNear Gram660ProofSharing.c235 Bool.false (nat_lit 56113196985936999) (nat_lit 9007199254740992) (nat_lit 5000561) (nat_lit 66000000000000000) Bool.false (nat_lit 884002492384675) (nat_lit 562949953421312) (nat_lit 10000033) (nat_lit 66000000000000000) Gram660ProofSharing.c296)

noncomputable def Gram660ProofSharing.c298 := (@Enclosure.Complex.IsNear.im_isNear Gram660ProofSharing.c234 Bool.true (nat_lit 100000) (nat_lit 400000) (nat_lit 0) (nat_lit 1) Bool.false (nat_lit 203064868) (nat_lit 400000) (nat_lit 0) (nat_lit 1) Gram660ProofSharing.c252)

noncomputable def Gram660ProofSharing.c299 := (@Enclosure.Complex.IsNear.im_isNear Gram660ProofSharing.c235 Bool.false (nat_lit 56113196985936999) (nat_lit 9007199254740992) (nat_lit 5000561) (nat_lit 66000000000000000) Bool.false (nat_lit 884002492384675) (nat_lit 562949953421312) (nat_lit 10000033) (nat_lit 66000000000000000) Gram660ProofSharing.c296)

noncomputable def Gram660ProofSharing.c300 := (↑Gram660ProofSharing.c8)

noncomputable def Gram660ProofSharing.c301 := (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) (Gram660ProofSharing.c233 : ℂ).re (Gram660ProofSharing.c300 : ℂ).re)

noncomputable def Gram660ProofSharing.c302 := (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) (Gram660ProofSharing.c233 : ℂ).im (Gram660ProofSharing.c300 : ℂ).im)

noncomputable def Gram660ProofSharing.c303 := (Enclosure.sfrac Bool.false (nat_lit 0) (nat_lit 1))

noncomputable def Gram660ProofSharing.c304 := (Enclosure.Real.IsNear.const Bool.false (nat_lit 0) (nat_lit 1))

noncomputable def Gram660ProofSharing.c305 := (@Enclosure.Complex.IsNear.mk Gram660ProofSharing.c256 Gram660ProofSharing.c303 Bool.false (nat_lit 1) (nat_lit 2) (nat_lit 0) (nat_lit 1) Bool.false (nat_lit 0) (nat_lit 1) (nat_lit 0) (nat_lit 1) Gram660ProofSharing.c261 Gram660ProofSharing.c304)

noncomputable def Gram660ProofSharing.c306 := (@Enclosure.Complex.IsNear.of_eq Gram660ProofSharing.c233 { re := Enclosure.sfrac Bool.false (nat_lit 1) (nat_lit 2), im := Enclosure.sfrac Bool.false (nat_lit 0) (nat_lit 1) } Bool.false (nat_lit 1) (nat_lit 2) (nat_lit 0) (nat_lit 1) Bool.false (nat_lit 0) (nat_lit 1) (nat_lit 0) (nat_lit 1) BSN.half_c_mk Gram660ProofSharing.c305)

noncomputable def Gram660ProofSharing.c307 := (@Enclosure.Complex.IsNear.re_isNear Gram660ProofSharing.c233 Bool.false (nat_lit 1) (nat_lit 2) (nat_lit 0) (nat_lit 1) Bool.false (nat_lit 0) (nat_lit 1) (nat_lit 0) (nat_lit 1) Gram660ProofSharing.c306)

noncomputable def Gram660ProofSharing.c308 := (Complex.ofReal_re Gram660ProofSharing.c8)

noncomputable def Gram660ProofSharing.c309 := (@Enclosure.Real.IsNear.of_eq (Gram660ProofSharing.c300 : ℂ).re Gram660ProofSharing.c8 Bool.false (nat_lit 3946810947) (nat_lit 2147483648) (nat_lit 1) (nat_lit 4294967296) Gram660ProofSharing.c308 Zeta.Certificates.Gram.gp6_cert._proof_1)

noncomputable def Gram660ProofSharing.c310 := (@Enclosure.Real.IsNear.mulLit_ff (Gram660ProofSharing.c233 : ℂ).re (Gram660ProofSharing.c300 : ℂ).re (nat_lit 1) (nat_lit 2) (nat_lit 0) (nat_lit 1) (nat_lit 3946810947) (nat_lit 2147483648) (nat_lit 1) (nat_lit 4294967296) (nat_lit 3946810947) (nat_lit 4294967296) (nat_lit 1) (nat_lit 8589934592) Gram660ProofSharing.c307 Gram660ProofSharing.c309 (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram660ProofSharing.c311 := (@Enclosure.Complex.IsNear.im_isNear Gram660ProofSharing.c233 Bool.false (nat_lit 1) (nat_lit 2) (nat_lit 0) (nat_lit 1) Bool.false (nat_lit 0) (nat_lit 1) (nat_lit 0) (nat_lit 1) Gram660ProofSharing.c306)

noncomputable def Gram660ProofSharing.c312 := (Complex.ofReal_im Gram660ProofSharing.c8)

noncomputable def Gram660ProofSharing.c313 := (@Eq.trans.{1} Real (Gram660ProofSharing.c300 : ℂ).im Gram660ProofSharing.c147 Gram660ProofSharing.c303 Gram660ProofSharing.c312 Enclosure.sfrac_zero_eq)

noncomputable def Gram660ProofSharing.c314 := (@Enclosure.Real.IsNear.of_eq (Gram660ProofSharing.c300 : ℂ).im Gram660ProofSharing.c303 Bool.false (nat_lit 0) (nat_lit 1) (nat_lit 0) (nat_lit 1) Gram660ProofSharing.c313 Gram660ProofSharing.c304)

noncomputable def Gram660ProofSharing.c315 := (@Enclosure.Real.IsNear.mulLit_ff (Gram660ProofSharing.c233 : ℂ).im (Gram660ProofSharing.c300 : ℂ).im (nat_lit 0) (nat_lit 1) (nat_lit 0) (nat_lit 1) (nat_lit 0) (nat_lit 1) (nat_lit 0) (nat_lit 1) (nat_lit 0) (nat_lit 1) (nat_lit 0) (nat_lit 1) Gram660ProofSharing.c311 Gram660ProofSharing.c314 (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram660ProofSharing.c316 := (@Enclosure.Real.IsNear.subLit_ff_p Gram660ProofSharing.c301 Gram660ProofSharing.c302 (nat_lit 3946810947) (nat_lit 4294967296) (nat_lit 1) (nat_lit 8589934592) (nat_lit 0) (nat_lit 1) (nat_lit 0) (nat_lit 1) (nat_lit 3946810947) (nat_lit 3946810947) (nat_lit 4294967296) (nat_lit 1) (nat_lit 8589934592) Gram660ProofSharing.c310 Gram660ProofSharing.c315 (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram660ProofSharing.c317 := (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) (Gram660ProofSharing.c233 : ℂ).re (Gram660ProofSharing.c300 : ℂ).im)

noncomputable def Gram660ProofSharing.c318 := (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) (Gram660ProofSharing.c233 : ℂ).im (Gram660ProofSharing.c300 : ℂ).re)

noncomputable def Gram660ProofSharing.c319 := (@Enclosure.Real.IsNear.mulLit_ff (Gram660ProofSharing.c233 : ℂ).re (Gram660ProofSharing.c300 : ℂ).im (nat_lit 1) (nat_lit 2) (nat_lit 0) (nat_lit 1) (nat_lit 0) (nat_lit 1) (nat_lit 0) (nat_lit 1) (nat_lit 0) (nat_lit 1) (nat_lit 0) (nat_lit 1) Gram660ProofSharing.c307 Gram660ProofSharing.c314 (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram660ProofSharing.c320 := (@Enclosure.Real.IsNear.mulLit_ff (Gram660ProofSharing.c233 : ℂ).im (Gram660ProofSharing.c300 : ℂ).re (nat_lit 0) (nat_lit 1) (nat_lit 0) (nat_lit 1) (nat_lit 3946810947) (nat_lit 2147483648) (nat_lit 1) (nat_lit 4294967296) (nat_lit 0) (nat_lit 1) (nat_lit 0) (nat_lit 1) Gram660ProofSharing.c311 Gram660ProofSharing.c309 (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram660ProofSharing.c321 := (@Enclosure.Real.IsNear.addLit_ff Gram660ProofSharing.c317 Gram660ProofSharing.c318 (nat_lit 0) (nat_lit 1) (nat_lit 0) (nat_lit 1) (nat_lit 0) (nat_lit 1) (nat_lit 0) (nat_lit 1) (nat_lit 0) (nat_lit 0) (nat_lit 1) (nat_lit 0) (nat_lit 1) Gram660ProofSharing.c319 Gram660ProofSharing.c320 (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram660ProofSharing.c322 := (@Enclosure.Complex.IsNear.mul Gram660ProofSharing.c233 Gram660ProofSharing.c300 Bool.false (nat_lit 3946810947) (nat_lit 4294967296) (nat_lit 1) (nat_lit 8589934592) Bool.false (nat_lit 0) (nat_lit 1) (nat_lit 0) (nat_lit 1) Gram660ProofSharing.c316 Gram660ProofSharing.c321)

noncomputable def Gram660ProofSharing.c323 := (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) Gram660ProofSharing.c32 (nat_lit 2))

noncomputable def Gram660ProofSharing.c324 := (bernoulli Gram660ProofSharing.c323)

noncomputable def Gram660ProofSharing.c325 := (@Rat.cast.{0} Complex Complex.instRatCast Gram660ProofSharing.c324)

noncomputable def Gram660ProofSharing.c326 := (@Nat.cast.{0} Complex Complex.instNatCast (nat_lit 2))

noncomputable def Gram660ProofSharing.c327 := (@HMul.hMul.{0, 0, 0} Complex Complex Complex (@instHMul.{0} Complex Complex.instMul) Gram660ProofSharing.c42 Gram660ProofSharing.c326)

noncomputable def Gram660ProofSharing.c328 := (@HSub.hSub.{0, 0, 0} Complex Complex Complex (@instHSub.{0} Complex Complex.instSub) Gram660ProofSharing.c327 Gram660ProofSharing.c30)

noncomputable def Gram660ProofSharing.c329 := (@HMul.hMul.{0, 0, 0} Complex Complex Complex (@instHMul.{0} Complex Complex.instMul) Gram660ProofSharing.c327 Gram660ProofSharing.c328)

noncomputable def Gram660ProofSharing.c330 := (@HDiv.hDiv.{0, 0, 0} Complex Complex Complex Gram660ProofSharing.c28 Gram660ProofSharing.c325 Gram660ProofSharing.c329)

noncomputable def Gram660ProofSharing.c331 := (@Nat.cast.{0} Int instNatCastInt (nat_lit 2))

noncomputable def Gram660ProofSharing.c332 := (@HMul.hMul.{0, 0, 0} Int Int Int (@instHMul.{0} Int Int.instMul) Gram660ProofSharing.c244 Gram660ProofSharing.c331)

noncomputable def Gram660ProofSharing.c333 := (@HSub.hSub.{0, 0, 0} Int Int Int (@instHSub.{0} Int Int.instSub) Gram660ProofSharing.c243 Gram660ProofSharing.c332)

noncomputable def Gram660ProofSharing.c334 := (@HPow.hPow.{0, 0, 0} Complex Int Complex Gram660ProofSharing.c242 Gram660ProofSharing.c47 Gram660ProofSharing.c333)

noncomputable def Gram660ProofSharing.c335 := (@HMul.hMul.{0, 0, 0} Complex Complex Complex (@instHMul.{0} Complex Complex.instMul) Gram660ProofSharing.c330 Gram660ProofSharing.c334)

noncomputable def Gram660ProofSharing.c336 := (nat_lit 2365454403706294875979163328069527)

noncomputable def Gram660ProofSharing.c337 := (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) Gram660ProofSharing.c32 (nat_lit 1))

noncomputable def Gram660ProofSharing.c338 := (bernoulli Gram660ProofSharing.c337)

noncomputable def Gram660ProofSharing.c339 := (@Rat.cast.{0} Complex Complex.instRatCast Gram660ProofSharing.c338)

noncomputable def Gram660ProofSharing.c340 := (@Nat.cast.{0} Complex Complex.instNatCast (nat_lit 1))

noncomputable def Gram660ProofSharing.c341 := (@HMul.hMul.{0, 0, 0} Complex Complex Complex (@instHMul.{0} Complex Complex.instMul) Gram660ProofSharing.c42 Gram660ProofSharing.c340)

noncomputable def Gram660ProofSharing.c342 := (@HSub.hSub.{0, 0, 0} Complex Complex Complex (@instHSub.{0} Complex Complex.instSub) Gram660ProofSharing.c341 Gram660ProofSharing.c30)

noncomputable def Gram660ProofSharing.c343 := (@HMul.hMul.{0, 0, 0} Complex Complex Complex (@instHMul.{0} Complex Complex.instMul) Gram660ProofSharing.c341 Gram660ProofSharing.c342)

noncomputable def Gram660ProofSharing.c344 := (@HDiv.hDiv.{0, 0, 0} Complex Complex Complex Gram660ProofSharing.c28 Gram660ProofSharing.c339 Gram660ProofSharing.c343)

noncomputable def Gram660ProofSharing.c345 := (@Nat.cast.{0} Int instNatCastInt (nat_lit 1))

noncomputable def Gram660ProofSharing.c346 := (@HMul.hMul.{0, 0, 0} Int Int Int (@instHMul.{0} Int Int.instMul) Gram660ProofSharing.c244 Gram660ProofSharing.c345)

noncomputable def Gram660ProofSharing.c347 := (@HSub.hSub.{0, 0, 0} Int Int Int (@instHSub.{0} Int Int.instSub) Gram660ProofSharing.c243 Gram660ProofSharing.c346)

noncomputable def Gram660ProofSharing.c348 := (@HPow.hPow.{0, 0, 0} Complex Int Complex Gram660ProofSharing.c242 Gram660ProofSharing.c47 Gram660ProofSharing.c347)

noncomputable def Gram660ProofSharing.c349 := (@HMul.hMul.{0, 0, 0} Complex Complex Complex (@instHMul.{0} Complex Complex.instMul) Gram660ProofSharing.c344 Gram660ProofSharing.c348)

noncomputable def Gram660ProofSharing.c350 := (@Enclosure.Complex.IsNear.mk Gram660ProofSharing.c303 Gram660ProofSharing.c303 Bool.false (nat_lit 0) (nat_lit 1) (nat_lit 0) (nat_lit 1) Bool.false (nat_lit 0) (nat_lit 1) (nat_lit 0) (nat_lit 1) Gram660ProofSharing.c304 Gram660ProofSharing.c304)

noncomputable def Gram660ProofSharing.c351 := (BSN.stirling_coeff_mk (nat_lit 1) (nat_lit 1) (nat_lit 6) Bool.false BSN.bern_real_1 (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram660ProofSharing.c352 := (Enclosure.sfrac Bool.false (nat_lit 1) (nat_lit 12))

noncomputable def Gram660ProofSharing.c353 := (Enclosure.Real.IsNear.const Bool.false (nat_lit 1) (nat_lit 12))

noncomputable def Gram660ProofSharing.c354 := (@Enclosure.Complex.IsNear.mk Gram660ProofSharing.c352 Gram660ProofSharing.c303 Bool.false (nat_lit 1) (nat_lit 12) (nat_lit 0) (nat_lit 1) Bool.false (nat_lit 0) (nat_lit 1) (nat_lit 0) (nat_lit 1) Gram660ProofSharing.c353 Gram660ProofSharing.c304)

noncomputable def Gram660ProofSharing.c355 := (@Enclosure.Complex.IsNear.of_eq Gram660ProofSharing.c344 { re := Enclosure.sfrac Bool.false (nat_lit 1) (nat_lit 12), im := Enclosure.sfrac Bool.false (nat_lit 0) (nat_lit 1) } Bool.false (nat_lit 1) (nat_lit 12) (nat_lit 0) (nat_lit 1) Bool.false (nat_lit 0) (nat_lit 1) (nat_lit 0) (nat_lit 1) Gram660ProofSharing.c351 Gram660ProofSharing.c354)

noncomputable def Gram660ProofSharing.c356 := (@Enclosure.Complex.IsNear.re_isNear Gram660ProofSharing.c344 Bool.false (nat_lit 1) (nat_lit 12) (nat_lit 0) (nat_lit 1) Bool.false (nat_lit 0) (nat_lit 1) (nat_lit 0) (nat_lit 1) Gram660ProofSharing.c355)

noncomputable def Gram660ProofSharing.c357 := (@Inv.inv.{0} Complex Complex.instInv Gram660ProofSharing.c50)

noncomputable def Gram660ProofSharing.c358 := (BSN.zpow_one_sub_two_mul Gram660ProofSharing.c47 (nat_lit 1) (nat_lit 1) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram660ProofSharing.c359 := (@instMulZeroOneClassOfSemiring.{0} Complex Complex.instSemiring)

noncomputable def Gram660ProofSharing.c360 := (@instMulZeroOneClassOfSemiring.{0} Real Real.semiring)

noncomputable def Gram660ProofSharing.c361 := (@MonoidWithZeroHom.{0, 0} Complex Real Gram660ProofSharing.c359 Gram660ProofSharing.c360)

noncomputable def Gram660ProofSharing.c362 := (@MonoidWithZeroHom.funLike.{0, 0} Complex Real Gram660ProofSharing.c359 Gram660ProofSharing.c360)

noncomputable def Gram660ProofSharing.c363 := (Enclosure.Complex.inv_re_eq_mul Gram660ProofSharing.c50)

noncomputable def Gram660ProofSharing.c364 := (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) (Gram660ProofSharing.c50 : ℂ).re (Gram660ProofSharing.c50 : ℂ).re)

noncomputable def Gram660ProofSharing.c365 := (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) (Gram660ProofSharing.c50 : ℂ).im (Gram660ProofSharing.c50 : ℂ).im)

noncomputable def Gram660ProofSharing.c366 := (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd) Gram660ProofSharing.c364 Gram660ProofSharing.c365)

noncomputable def Gram660ProofSharing.c367 := (Enclosure.Complex.normSq_eq_mul_add_mul Gram660ProofSharing.c50)

noncomputable def Gram660ProofSharing.c368 := (@Enclosure.Real.IsNear.mulLit_ff (Gram660ProofSharing.c50 : ℂ).re (Gram660ProofSharing.c50 : ℂ).re (nat_lit 100000) (nat_lit 400000) (nat_lit 0) (nat_lit 1) (nat_lit 100000) (nat_lit 400000) (nat_lit 0) (nat_lit 1) (nat_lit 1) (nat_lit 16) (nat_lit 0) (nat_lit 1) Gram660ProofSharing.c65 Gram660ProofSharing.c65 (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram660ProofSharing.c369 := (@Enclosure.Real.IsNear.mulLit_ff (Gram660ProofSharing.c50 : ℂ).im (Gram660ProofSharing.c50 : ℂ).im (nat_lit 203064868) (nat_lit 400000) (nat_lit 0) (nat_lit 1) (nat_lit 203064868) (nat_lit 400000) (nat_lit 0) (nat_lit 1) (nat_lit 2577208788491089) (nat_lit 10000000000) (nat_lit 0) (nat_lit 1) Gram660ProofSharing.c68 Gram660ProofSharing.c68 (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram660ProofSharing.c370 := (@Enclosure.Real.IsNear.addLit_ff Gram660ProofSharing.c364 Gram660ProofSharing.c365 (nat_lit 1) (nat_lit 16) (nat_lit 0) (nat_lit 1) (nat_lit 2577208788491089) (nat_lit 10000000000) (nat_lit 0) (nat_lit 1) (nat_lit 41235350615857424) (nat_lit 2577209413491089) (nat_lit 10000000000) (nat_lit 0) (nat_lit 1) Gram660ProofSharing.c368 Gram660ProofSharing.c369 (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram660ProofSharing.c371 := (@Neg.neg.{0} Real Real.instNeg (Gram660ProofSharing.c50 : ℂ).im)

noncomputable def Gram660ProofSharing.c372 := (Enclosure.Complex.inv_im_eq_mul Gram660ProofSharing.c50)

noncomputable def Gram660ProofSharing.c373 := (@Enclosure.Real.IsNear.neg (Gram660ProofSharing.c50 : ℂ).im Bool.false (nat_lit 203064868) (nat_lit 400000) (nat_lit 0) (nat_lit 1) Gram660ProofSharing.c68)

noncomputable def Gram660ProofSharing.c374 := (@Enclosure.Complex.IsNear.im_isNear Gram660ProofSharing.c344 Bool.false (nat_lit 1) (nat_lit 12) (nat_lit 0) (nat_lit 1) Bool.false (nat_lit 0) (nat_lit 1) (nat_lit 0) (nat_lit 1) Gram660ProofSharing.c355)

noncomputable def Gram660ProofSharing.c375 := (nat_lit 12379400392853802748991242240000000000)

noncomputable def Gram660ProofSharing.c376 := (BSN.stirling_coeff_mk (nat_lit 2) (nat_lit 1) (nat_lit 30) Bool.true BSN.bern_real_2 (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram660ProofSharing.c377 := (Enclosure.sfrac Bool.true (nat_lit 1) (nat_lit 360))

noncomputable def Gram660ProofSharing.c378 := (Enclosure.Real.IsNear.const Bool.true (nat_lit 1) (nat_lit 360))

noncomputable def Gram660ProofSharing.c379 := (@Enclosure.Complex.IsNear.mk Gram660ProofSharing.c377 Gram660ProofSharing.c303 Bool.true (nat_lit 1) (nat_lit 360) (nat_lit 0) (nat_lit 1) Bool.false (nat_lit 0) (nat_lit 1) (nat_lit 0) (nat_lit 1) Gram660ProofSharing.c378 Gram660ProofSharing.c304)

noncomputable def Gram660ProofSharing.c380 := (@Enclosure.Complex.IsNear.of_eq Gram660ProofSharing.c330 { re := Enclosure.sfrac Bool.true (nat_lit 1) (nat_lit 360), im := Enclosure.sfrac Bool.false (nat_lit 0) (nat_lit 1) } Bool.true (nat_lit 1) (nat_lit 360) (nat_lit 0) (nat_lit 1) Bool.false (nat_lit 0) (nat_lit 1) (nat_lit 0) (nat_lit 1) Gram660ProofSharing.c376 Gram660ProofSharing.c379)

noncomputable def Gram660ProofSharing.c381 := (@Enclosure.Complex.IsNear.re_isNear Gram660ProofSharing.c330 Bool.true (nat_lit 1) (nat_lit 360) (nat_lit 0) (nat_lit 1) Bool.false (nat_lit 0) (nat_lit 1) (nat_lit 0) (nat_lit 1) Gram660ProofSharing.c380)

noncomputable def Gram660ProofSharing.c382 := (nat_lit 309485009821345068724781056000000000000000)

noncomputable def Gram660ProofSharing.c383 := (@Inv.inv.{0} Complex Complex.instInv Gram660ProofSharing.c48)

noncomputable def Gram660ProofSharing.c384 := (BSN.zpow_one_sub_two_mul Gram660ProofSharing.c47 (nat_lit 2) (nat_lit 3) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram660ProofSharing.c385 := (Enclosure.Complex.inv_re_eq_mul Gram660ProofSharing.c48)

noncomputable def Gram660ProofSharing.c386 := (@Enclosure.Complex.IsNear.re_isNear Gram660ProofSharing.c48 Bool.true (nat_lit 7731625740473267) (nat_lit 40000000000) (nat_lit 0) (nat_lit 1) Bool.true (nat_lit 130835045424188851740313) (nat_lit 1000000000000000) (nat_lit 0) (nat_lit 1) Zeta.Certificates.Gram.gp6_cert._proof_2)

noncomputable def Gram660ProofSharing.c387 := (nat_lit 17117846472422429409816940284648776554414337969)

noncomputable def Gram660ProofSharing.c388 := (nat_lit 1000000000000000000000000000000)

noncomputable def Gram660ProofSharing.c389 := (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) (Gram660ProofSharing.c48 : ℂ).re (Gram660ProofSharing.c48 : ℂ).re)

noncomputable def Gram660ProofSharing.c390 := (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) (Gram660ProofSharing.c48 : ℂ).im (Gram660ProofSharing.c48 : ℂ).im)

noncomputable def Gram660ProofSharing.c391 := (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd) Gram660ProofSharing.c389 Gram660ProofSharing.c390)

noncomputable def Gram660ProofSharing.c392 := (Enclosure.Complex.normSq_eq_mul_add_mul Gram660ProofSharing.c48)

noncomputable def Gram660ProofSharing.c393 := (nat_lit 59778036590748794238409141653289)

noncomputable def Gram660ProofSharing.c394 := (nat_lit 17117809111149560191820541278935243248789337969)

noncomputable def Gram660ProofSharing.c395 := (nat_lit 27388554355875887055707104455438042487062940750400000000000000000000)

noncomputable def Gram660ProofSharing.c396 := (@Enclosure.Real.IsNear.mulLit_tt (Gram660ProofSharing.c48 : ℂ).re (Gram660ProofSharing.c48 : ℂ).re (nat_lit 7731625740473267) (nat_lit 40000000000) (nat_lit 0) (nat_lit 1) (nat_lit 7731625740473267) (nat_lit 40000000000) (nat_lit 0) (nat_lit 1) Gram660ProofSharing.c393 (nat_lit 1600000000000000000000) (nat_lit 0) (nat_lit 1) Gram660ProofSharing.c386 Gram660ProofSharing.c386 (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram660ProofSharing.c397 := (@Enclosure.Complex.IsNear.im_isNear Gram660ProofSharing.c48 Bool.true (nat_lit 7731625740473267) (nat_lit 40000000000) (nat_lit 0) (nat_lit 1) Bool.true (nat_lit 130835045424188851740313) (nat_lit 1000000000000000) (nat_lit 0) (nat_lit 1) Zeta.Certificates.Gram.gp6_cert._proof_2)

noncomputable def Gram660ProofSharing.c398 := (@Enclosure.Real.IsNear.mulLit_tt (Gram660ProofSharing.c48 : ℂ).im (Gram660ProofSharing.c48 : ℂ).im (nat_lit 130835045424188851740313) (nat_lit 1000000000000000) (nat_lit 0) (nat_lit 1) (nat_lit 130835045424188851740313) (nat_lit 1000000000000000) (nat_lit 0) (nat_lit 1) Gram660ProofSharing.c394 Gram660ProofSharing.c388 (nat_lit 0) (nat_lit 1) Gram660ProofSharing.c397 Gram660ProofSharing.c397 (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram660ProofSharing.c399 := (@Enclosure.Real.IsNear.addLit_ff Gram660ProofSharing.c389 Gram660ProofSharing.c390 Gram660ProofSharing.c393 (nat_lit 1600000000000000000000) (nat_lit 0) (nat_lit 1) Gram660ProofSharing.c394 Gram660ProofSharing.c388 (nat_lit 0) (nat_lit 1) Gram660ProofSharing.c395 Gram660ProofSharing.c387 Gram660ProofSharing.c388 (nat_lit 0) (nat_lit 1) Gram660ProofSharing.c396 Gram660ProofSharing.c398 (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram660ProofSharing.c400 := (@Neg.neg.{0} Real Real.instNeg (Gram660ProofSharing.c48 : ℂ).im)

noncomputable def Gram660ProofSharing.c401 := (Enclosure.Complex.inv_im_eq_mul Gram660ProofSharing.c48)

noncomputable def Gram660ProofSharing.c402 := (@Enclosure.Real.IsNear.neg (Gram660ProofSharing.c48 : ℂ).im Bool.true (nat_lit 130835045424188851740313) (nat_lit 1000000000000000) (nat_lit 0) (nat_lit 1) Gram660ProofSharing.c397)

noncomputable def Gram660ProofSharing.c403 := (@Enclosure.Complex.IsNear.im_isNear Gram660ProofSharing.c330 Bool.true (nat_lit 1) (nat_lit 360) (nat_lit 0) (nat_lit 1) Bool.false (nat_lit 0) (nat_lit 1) (nat_lit 0) (nat_lit 1) Gram660ProofSharing.c380)

noncomputable def Gram660ProofSharing.c404 := (BSN.logSumC Gram660ProofSharing.c39 (nat_lit 0))

noncomputable def Gram660ProofSharing.c405 := (Enclosure.sfrac Bool.false (nat_lit 98304000000000000000000000) Gram660ProofSharing.c106)

noncomputable def Gram660ProofSharing.c406 := (@Monoid.toNPow.{0} Real Real.instMonoid)

noncomputable def Gram660ProofSharing.c407 := (@NPow.toPow.{0} Real Gram660ProofSharing.c406)

noncomputable def Gram660ProofSharing.c408 := (@instHPow.{0, 0} Real Nat Gram660ProofSharing.c407)

noncomputable def Gram660ProofSharing.c409 := (@HPow.hPow.{0, 0, 0} Real Nat Real Gram660ProofSharing.c408 Gram660ProofSharing.c7 (nat_lit 4))

noncomputable def Gram660ProofSharing.c410 := (@Inv.inv.{0} Real Real.instInv Gram660ProofSharing.c409)

noncomputable def Gram660ProofSharing.c411 := (nat_lit 611446774371975769155682509262542103857872115376664175900625)

noncomputable def Gram660ProofSharing.c412 := (nat_lit 392318858461667547739736838950479151006397215279002157056)

noncomputable def Gram660ProofSharing.c413 := (nat_lit 19652562622312316682495810535216024035134795670488584765154486969712234385047)

noncomputable def Gram660ProofSharing.c414 := (nat_lit 9903520314283042199192993792000000000000000000000000000000000000000000000000000000000000)

noncomputable def Gram660ProofSharing.c415 := (@HPow.hPow.{0, 0, 0} Real Nat Real Gram660ProofSharing.c408 Gram660ProofSharing.c7 (nat_lit 3))

noncomputable def Gram660ProofSharing.c416 := (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) Gram660ProofSharing.c415 Gram660ProofSharing.c7)

noncomputable def Gram660ProofSharing.c417 := (BSN.pow_succ_r Gram660ProofSharing.c7 (nat_lit 3) (nat_lit 4) (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram660ProofSharing.c418 := (nat_lit 691463075802508163054686763366652189853178875)

noncomputable def Gram660ProofSharing.c419 := (nat_lit 2787593149816327892691964784081045188247552)

noncomputable def Gram660ProofSharing.c420 := (nat_lit 2184744797947834540264818678394244808492865883128339)

noncomputable def Gram660ProofSharing.c421 := (nat_lit 9223372036854775808000000000000000000000000000000000000000000000)

noncomputable def Gram660ProofSharing.c422 := (@HPow.hPow.{0, 0, 0} Real Nat Real Gram660ProofSharing.c408 Gram660ProofSharing.c7 (nat_lit 2))

noncomputable def Gram660ProofSharing.c423 := (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) Gram660ProofSharing.c422 Gram660ProofSharing.c7)

noncomputable def Gram660ProofSharing.c424 := (BSN.pow_succ_r Gram660ProofSharing.c7 (nat_lit 2) (nat_lit 3) (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram660ProofSharing.c425 := (nat_lit 1073741824000000000000000000000000000000)

noncomputable def Gram660ProofSharing.c426 := (@HPow.hPow.{0, 0, 0} Real Nat Real Gram660ProofSharing.c408 Gram660ProofSharing.c7 (nat_lit 1))

noncomputable def Gram660ProofSharing.c427 := (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) Gram660ProofSharing.c426 Gram660ProofSharing.c7)

noncomputable def Gram660ProofSharing.c428 := (BSN.pow_succ_r Gram660ProofSharing.c7 (nat_lit 1) (nat_lit 2) (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram660ProofSharing.c429 := (BSN.pow_one_r Gram660ProofSharing.c7)

noncomputable def Gram660ProofSharing.c430 := (@Enclosure.Real.IsNear.of_eq Gram660ProofSharing.c7 Gram660ProofSharing.c10 Bool.false (nat_lit 884279719003555) (nat_lit 140737488355328) (nat_lit 1) (nat_lit 500000000000000) BSN.two_pi_eq Gram660ProofSharing.c13)

noncomputable def Gram660ProofSharing.c431 := (@Enclosure.Real.IsNear.of_eq Gram660ProofSharing.c426 Gram660ProofSharing.c7 Bool.false (nat_lit 884279719003555) (nat_lit 140737488355328) (nat_lit 1) (nat_lit 500000000000000) Gram660ProofSharing.c429 Gram660ProofSharing.c430)

noncomputable def Gram660ProofSharing.c432 := (@Enclosure.Real.IsNear.mulLit_ff Gram660ProofSharing.c426 Gram660ProofSharing.c7 (nat_lit 884279719003555) (nat_lit 140737488355328) (nat_lit 1) (nat_lit 500000000000000) (nat_lit 884279719003555) (nat_lit 140737488355328) (nat_lit 1) (nat_lit 500000000000000) (nat_lit 781950621441006189802102638025) (nat_lit 19807040628566084398385987584) (nat_lit 26986075409044041160201671) Gram660ProofSharing.c425 Gram660ProofSharing.c431 Gram660ProofSharing.c430 (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram660ProofSharing.c433 := (@Enclosure.Real.IsNear.of_eq Gram660ProofSharing.c422 Gram660ProofSharing.c427 Bool.false (nat_lit 781950621441006189802102638025) (nat_lit 19807040628566084398385987584) (nat_lit 26986075409044041160201671) Gram660ProofSharing.c425 Gram660ProofSharing.c428 Gram660ProofSharing.c432)

noncomputable def Gram660ProofSharing.c434 := (@Enclosure.Real.IsNear.mulLit_ff Gram660ProofSharing.c422 Gram660ProofSharing.c7 (nat_lit 781950621441006189802102638025) (nat_lit 19807040628566084398385987584) (nat_lit 26986075409044041160201671) Gram660ProofSharing.c425 (nat_lit 884279719003555) (nat_lit 140737488355328) (nat_lit 1) (nat_lit 500000000000000) Gram660ProofSharing.c418 Gram660ProofSharing.c419 Gram660ProofSharing.c420 Gram660ProofSharing.c421 Gram660ProofSharing.c433 Gram660ProofSharing.c430 (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram660ProofSharing.c435 := (@Enclosure.Real.IsNear.of_eq Gram660ProofSharing.c415 Gram660ProofSharing.c423 Bool.false Gram660ProofSharing.c418 Gram660ProofSharing.c419 Gram660ProofSharing.c420 Gram660ProofSharing.c421 Gram660ProofSharing.c424 Gram660ProofSharing.c434)

noncomputable def Gram660ProofSharing.c436 := (@Enclosure.Real.IsNear.mulLit_ff Gram660ProofSharing.c415 Gram660ProofSharing.c7 Gram660ProofSharing.c418 Gram660ProofSharing.c419 Gram660ProofSharing.c420 Gram660ProofSharing.c421 (nat_lit 884279719003555) (nat_lit 140737488355328) (nat_lit 1) (nat_lit 500000000000000) Gram660ProofSharing.c411 Gram660ProofSharing.c412 Gram660ProofSharing.c413 Gram660ProofSharing.c414 Gram660ProofSharing.c435 Gram660ProofSharing.c430 (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram660ProofSharing.c437 := (@Enclosure.Real.IsNear.of_eq Gram660ProofSharing.c409 Gram660ProofSharing.c416 Bool.false Gram660ProofSharing.c411 Gram660ProofSharing.c412 Gram660ProofSharing.c413 Gram660ProofSharing.c414 Gram660ProofSharing.c417 Gram660ProofSharing.c436)

noncomputable def Gram660ProofSharing.c438 := (@Enclosure.Real.IsNear.inv_image Gram660ProofSharing.c409 Gram660ProofSharing.c411 Gram660ProofSharing.c412 Gram660ProofSharing.c413 Gram660ProofSharing.c414 (nat_lit 5511507) (nat_lit 5511508) (nat_lit 8589934592) Gram660ProofSharing.c437 (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram660ProofSharing.c439 := (@Enclosure.Real.IsNear.recentre' Gram660ProofSharing.c410 Bool.false (nat_lit 11023015) (nat_lit 17179869184) (nat_lit 1) (nat_lit 17179869184) (nat_lit 11023015) (nat_lit 17179869184) (nat_lit 1) (nat_lit 17179869184) Gram660ProofSharing.c438 (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram660ProofSharing.c440 := (nat_lit 9702058186543205271292555665472215655577)

noncomputable def Gram660ProofSharing.c441 := (nat_lit 297105609428491265975789813760000000000000000)

noncomputable def Gram660ProofSharing.c442 := (nat_lit 960235542736167185728596257875877017576063)

noncomputable def Gram660ProofSharing.c443 := (nat_lit 6127803194462632360750664908800000000000000000000)

noncomputable def Gram660ProofSharing.c444 := (nat_lit 1700354341375526857418991442287376)

noncomputable def Gram660ProofSharing.c445 := (riemannSiegelThetaApproximant (nat_lit 2) (nat_lit 0) Gram660ProofSharing.c107)

noncomputable def Gram660ProofSharing.c446 := (nat_lit 616033977649830098474684466940555665472215655577)

noncomputable def Gram660ProofSharing.c447 := (nat_lit 960231498386058840391238162437037209576063)

noncomputable def Gram660ProofSharing.c448 := (Complex.Stirling.logGammaStirling (nat_lit 2) Gram660ProofSharing.c112)

noncomputable def Gram660ProofSharing.c449 := (@HDiv.hDiv.{0, 0, 0} Real Real Real Gram660ProofSharing.c15 Gram660ProofSharing.c107 Gram660ProofSharing.c6)

noncomputable def Gram660ProofSharing.c450 := (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) Gram660ProofSharing.c449 (Real.log Real.pi))

noncomputable def Gram660ProofSharing.c451 := (nat_lit 788692765382121620978312940837823684672215655577)

noncomputable def Gram660ProofSharing.c452 := (nat_lit 235929368810336956917694994437037209576063)

noncomputable def Gram660ProofSharing.c453 := (nat_lit 1580745266835730262762051154792319967151221)

noncomputable def Gram660ProofSharing.c454 := (nat_lit 1980704062856608439838598758400000000000)

noncomputable def Gram660ProofSharing.c455 := (nat_lit 29510781529282377569260417479746605910429)

noncomputable def Gram660ProofSharing.c456 := (nat_lit 382987699653914522546916556800000000000000000000)

noncomputable def Gram660ProofSharing.c457 := (@HSub.hSub.{0, 0, 0} Complex Complex Complex (@instHSub.{0} Complex Complex.instSub) Gram660ProofSharing.c112 Gram660ProofSharing.c233)

noncomputable def Gram660ProofSharing.c458 := (Complex.log Gram660ProofSharing.c112)

noncomputable def Gram660ProofSharing.c459 := (@HMul.hMul.{0, 0, 0} Complex Complex Complex (@instHMul.{0} Complex Complex.instMul) Gram660ProofSharing.c457 Gram660ProofSharing.c458)

noncomputable def Gram660ProofSharing.c460 := (@HSub.hSub.{0, 0, 0} Complex Complex Complex (@instHSub.{0} Complex Complex.instSub) Gram660ProofSharing.c459 Gram660ProofSharing.c112)

noncomputable def Gram660ProofSharing.c461 := (@HAdd.hAdd.{0, 0, 0} Complex Complex Complex (@instHAdd.{0} Complex Complex.instAdd) Gram660ProofSharing.c460 Gram660ProofSharing.c238)

noncomputable def Gram660ProofSharing.c462 := (nat_lit 160113808885777267477017632848779)

noncomputable def Gram660ProofSharing.c463 := (nat_lit 17826336565709475958547388825600000000000)

noncomputable def Gram660ProofSharing.c464 := (nat_lit 48770223024807723057467307220927784344423)

noncomputable def Gram660ProofSharing.c465 := (nat_lit 8372708177525518931407440977453)

noncomputable def Gram660ProofSharing.c466 := (nat_lit 891316828285473797927369441280000000000000000)

noncomputable def Gram660ProofSharing.c467 := (BSN.w_sub_half_zero_mk Gram660ProofSharing.c107 Bool.false (nat_lit 101532437) (nat_lit 100000) Gram660ProofSharing.c121 (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram660ProofSharing.c468 := (@Enclosure.Complex.IsNear.mk Gram660ProofSharing.c249 Gram660ProofSharing.c123 Bool.true (nat_lit 100000) (nat_lit 400000) (nat_lit 0) (nat_lit 1) Bool.false (nat_lit 203064874) (nat_lit 400000) (nat_lit 0) (nat_lit 1) Gram660ProofSharing.c250 Gram660ProofSharing.c124)

noncomputable def Gram660ProofSharing.c469 := (@Enclosure.Complex.IsNear.of_eq Gram660ProofSharing.c457 { re := Enclosure.sfrac Bool.true (nat_lit 100000) (nat_lit 400000), im := Enclosure.sfrac Bool.false (nat_lit 203064874) (nat_lit 400000) } Bool.true (nat_lit 100000) (nat_lit 400000) (nat_lit 0) (nat_lit 1) Bool.false (nat_lit 203064874) (nat_lit 400000) (nat_lit 0) (nat_lit 1) Gram660ProofSharing.c467 Gram660ProofSharing.c468)

noncomputable def Gram660ProofSharing.c470 := (@Enclosure.Complex.IsNear.re_isNear Gram660ProofSharing.c457 Bool.true (nat_lit 100000) (nat_lit 400000) (nat_lit 0) (nat_lit 1) Bool.false (nat_lit 203064874) (nat_lit 400000) (nat_lit 0) (nat_lit 1) Gram660ProofSharing.c469)

noncomputable def Gram660ProofSharing.c471 := (Complex.log { re := Enclosure.sfrac Bool.false (nat_lit 100000) (nat_lit 400000), im := Enclosure.sfrac Bool.false (nat_lit 203064874) (nat_lit 400000) })

noncomputable def Gram660ProofSharing.c472 := (@congrArg.{1, 1} Complex Complex Gram660ProofSharing.c112 { re := Enclosure.sfrac Bool.false (nat_lit 100000) (nat_lit 400000), im := Enclosure.sfrac Bool.false (nat_lit 203064874) (nat_lit 400000) } Complex.log Gram660ProofSharing.c122)

noncomputable def Gram660ProofSharing.c473 := (Enclosure.sfrac Bool.false (nat_lit 41235353052635876) (nat_lit 160000000000))

noncomputable def Gram660ProofSharing.c474 := (Real.log Gram660ProofSharing.c473)

noncomputable def Gram660ProofSharing.c475 := (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) Gram660ProofSharing.c256 Gram660ProofSharing.c474)

noncomputable def Gram660ProofSharing.c476 := (Enclosure.clog_re_eq (nat_lit 100000) (nat_lit 203064874) (nat_lit 400000) (nat_lit 41235353052635876) (nat_lit 160000000000) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram660ProofSharing.c477 := (@Nat.cast.{0} Real Real.instNatCast (nat_lit 41235353052635876))

noncomputable def Gram660ProofSharing.c478 := (@HDiv.hDiv.{0, 0, 0} Real Real Real Gram660ProofSharing.c15 Gram660ProofSharing.c477 Gram660ProofSharing.c263)

noncomputable def Gram660ProofSharing.c479 := (Real.log Gram660ProofSharing.c478)

noncomputable def Gram660ProofSharing.c480 := (nat_lit 10352574084965639832603727956964365481189563943267085315331895347400564737130257631596012876560478801564607665019790642360069768275533978561046485958841001434793033839702792769863635638101581728570519350824922394070222400714941406547584868966026158204175163493700166986356705764490393989443749267048239965761939155251280045585872687941981254451200)

noncomputable def Gram660ProofSharing.c481 := (nat_lit 391419603504119959163585141385085384205544033212118425302884895328950083323013841107580934334598709598127460169638997798998497086474301605561650391510188436996245501149754923614690719116765853795545481964644483695460015197278906638217843454345346300789906278484443099382065966616312452199907418935837587641806274141159886523023650027724938936320)

noncomputable def Gram660ProofSharing.c482 := (nat_lit 89226447672973518522913685001903201954398983629302634045743431090042796243940804797081862705016162566649764888922627564805121424134993873967104495346073608178133920720708325956157606292093825134893435722758325968838667233047406735060858324304399233480656557994606592501811886451962454923894751015011072036890659760108044522951488307200)

noncomputable def Gram660ProofSharing.c483 := (BSN.artanhP (nat_lit 20263833052635876))

noncomputable def Gram660ProofSharing.c484 := (BSN.artanhQ (nat_lit 62206873052635876))

noncomputable def Gram660ProofSharing.c485 := (@BSN.binarySplit_of_base10 Gram660ProofSharing.c483 Gram660ProofSharing.c484 (nat_lit 0) (nat_lit 10) Gram660ProofSharing.c481 Gram660ProofSharing.c480 Gram660ProofSharing.c482 (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram660ProofSharing.c486 := (BSN.log_dyadic_bound (nat_lit 20263833052635876) (nat_lit 62206873052635876) (nat_lit 11) (nat_lit 10) Gram660ProofSharing.c480 (nat_lit 17179869184) (nat_lit 6600000000) Gram660ProofSharing.c481 Gram660ProofSharing.c482 (nat_lit 11615836039) (nat_lit 82470706105271752) (nat_lit 41943040000000000) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) Gram660ProofSharing.c485 (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram660ProofSharing.c487 := (BSN.log_rat_reduce_isNear (nat_lit 41235353052635876) (nat_lit 160000000000) (nat_lit 17) (nat_lit 82470706105271752) (nat_lit 41943040000000000) (nat_lit 11615836039) (nat_lit 17179869184) (nat_lit 24973259072661432) (nat_lit 36028797018963968) (nat_lit 6600000000) (nat_lit 1000000000000000) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) Gram660ProofSharing.c486 BSN.log2_near_15 (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram660ProofSharing.c488 := (@Enclosure.Real.IsNear.recentre' Gram660ProofSharing.c479 Bool.false (nat_lit 7712139106284594818132738048) (nat_lit 618970019642690137449562112) (nat_lit 1000112200000000) (nat_lit 6600000000000000000000000) (nat_lit 56113197252013159) (nat_lit 4503599627370496) (nat_lit 5000561) (nat_lit 33000000000000000) Gram660ProofSharing.c487 (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram660ProofSharing.c489 := (BSN.isNear_log_sfrac (nat_lit 41235353052635876) (nat_lit 160000000000) (nat_lit 56113197252013159) (nat_lit 4503599627370496) (nat_lit 5000561) (nat_lit 33000000000000000) Bool.false Gram660ProofSharing.c488)

noncomputable def Gram660ProofSharing.c490 := (@Enclosure.Real.IsNear.mulLit_ff Gram660ProofSharing.c256 Gram660ProofSharing.c474 (nat_lit 1) (nat_lit 2) (nat_lit 0) (nat_lit 1) (nat_lit 56113197252013159) (nat_lit 4503599627370496) (nat_lit 5000561) (nat_lit 33000000000000000) (nat_lit 56113197252013159) (nat_lit 9007199254740992) (nat_lit 5000561) (nat_lit 66000000000000000) Gram660ProofSharing.c261 Gram660ProofSharing.c489 (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram660ProofSharing.c491 := (@Enclosure.Real.IsNear.of_eq (Gram660ProofSharing.c471 : ℂ).re Gram660ProofSharing.c475 Bool.false (nat_lit 56113197252013159) (nat_lit 9007199254740992) (nat_lit 5000561) (nat_lit 66000000000000000) Gram660ProofSharing.c476 Gram660ProofSharing.c490)

noncomputable def Gram660ProofSharing.c492 := (@Nat.cast.{0} Real Real.instNatCast (nat_lit 203064874))

noncomputable def Gram660ProofSharing.c493 := (@HDiv.hDiv.{0, 0, 0} Real Real Real Gram660ProofSharing.c15 Gram660ProofSharing.c492 Gram660ProofSharing.c279)

noncomputable def Gram660ProofSharing.c494 := (Real.arctan Gram660ProofSharing.c493)

noncomputable def Gram660ProofSharing.c495 := (Enclosure.clog_im_eq (nat_lit 100000) (nat_lit 203064874) (nat_lit 400000) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram660ProofSharing.c496 := (@HDiv.hDiv.{0, 0, 0} Real Real Real Gram660ProofSharing.c15 Gram660ProofSharing.c279 Gram660ProofSharing.c492)

noncomputable def Gram660ProofSharing.c497 := (Real.arctan Gram660ProofSharing.c496)

noncomputable def Gram660ProofSharing.c498 := (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) Gram660ProofSharing.c283 Gram660ProofSharing.c497)

noncomputable def Gram660ProofSharing.c499 := (BSN.arctan_recip (nat_lit 203064874) (nat_lit 100000) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram660ProofSharing.c500 := (@BSN.binarySplit_of_le (BSN.arctanEvenP (nat_lit 100000)) (BSN.arctanEvenQ (nat_lit 203064874)) (nat_lit 0) (nat_lit 0) (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram660ProofSharing.c501 := (@BSN.binarySplit_of_le (BSN.arctanOddP (nat_lit 100000)) (BSN.arctanOddQ (nat_lit 203064874)) (nat_lit 0) (nat_lit 0) (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram660ProofSharing.c502 := (BSN.arctan_dyadic_bound_f (nat_lit 100000) (nat_lit 203064874) (nat_lit 1) (nat_lit 0) (nat_lit 17179869184) (nat_lit 6600000000) (nat_lit 0) (nat_lit 1) (nat_lit 1) (nat_lit 0) (nat_lit 1) (nat_lit 1) (nat_lit 8460285) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) Gram660ProofSharing.c500 Gram660ProofSharing.c501 (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram660ProofSharing.c503 := (@Enclosure.Real.IsNear.subLit_ff_p Gram660ProofSharing.c283 Gram660ProofSharing.c497 (nat_lit 884279719003555) (nat_lit 562949953421312) (nat_lit 1) (nat_lit 2000000000000000) (nat_lit 8460285) (nat_lit 17179869184) (nat_lit 1) (nat_lit 6600000000) (nat_lit 15187047177498672706355200) (nat_lit 884002492384675) (nat_lit 562949953421312) (nat_lit 10000033) (nat_lit 66000000000000000) Gram660ProofSharing.c288 Gram660ProofSharing.c502 (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram660ProofSharing.c504 := (@Enclosure.Real.IsNear.of_eq Gram660ProofSharing.c494 Gram660ProofSharing.c498 Bool.false (nat_lit 884002492384675) (nat_lit 562949953421312) (nat_lit 10000033) (nat_lit 66000000000000000) Gram660ProofSharing.c499 Gram660ProofSharing.c503)

noncomputable def Gram660ProofSharing.c505 := (@Enclosure.Real.IsNear.of_eq (Gram660ProofSharing.c471 : ℂ).im Gram660ProofSharing.c494 Bool.false (nat_lit 884002492384675) (nat_lit 562949953421312) (nat_lit 10000033) (nat_lit 66000000000000000) Gram660ProofSharing.c495 Gram660ProofSharing.c504)

noncomputable def Gram660ProofSharing.c506 := (@Enclosure.Complex.IsNear.of_parts Gram660ProofSharing.c471 Bool.false (nat_lit 56113197252013159) (nat_lit 9007199254740992) (nat_lit 5000561) (nat_lit 66000000000000000) Bool.false (nat_lit 884002492384675) (nat_lit 562949953421312) (nat_lit 10000033) (nat_lit 66000000000000000) Gram660ProofSharing.c491 Gram660ProofSharing.c505)

noncomputable def Gram660ProofSharing.c507 := (@Enclosure.Complex.IsNear.of_eq Gram660ProofSharing.c458 Gram660ProofSharing.c471 Bool.false (nat_lit 56113197252013159) (nat_lit 9007199254740992) (nat_lit 5000561) (nat_lit 66000000000000000) Bool.false (nat_lit 884002492384675) (nat_lit 562949953421312) (nat_lit 10000033) (nat_lit 66000000000000000) Gram660ProofSharing.c472 Gram660ProofSharing.c506)

noncomputable def Gram660ProofSharing.c508 := (@Enclosure.Complex.IsNear.re_isNear Gram660ProofSharing.c458 Bool.false (nat_lit 56113197252013159) (nat_lit 9007199254740992) (nat_lit 5000561) (nat_lit 66000000000000000) Bool.false (nat_lit 884002492384675) (nat_lit 562949953421312) (nat_lit 10000033) (nat_lit 66000000000000000) Gram660ProofSharing.c507)

noncomputable def Gram660ProofSharing.c509 := (@Enclosure.Complex.IsNear.im_isNear Gram660ProofSharing.c457 Bool.true (nat_lit 100000) (nat_lit 400000) (nat_lit 0) (nat_lit 1) Bool.false (nat_lit 203064874) (nat_lit 400000) (nat_lit 0) (nat_lit 1) Gram660ProofSharing.c469)

noncomputable def Gram660ProofSharing.c510 := (@Enclosure.Complex.IsNear.im_isNear Gram660ProofSharing.c458 Bool.false (nat_lit 56113197252013159) (nat_lit 9007199254740992) (nat_lit 5000561) (nat_lit 66000000000000000) Bool.false (nat_lit 884002492384675) (nat_lit 562949953421312) (nat_lit 10000033) (nat_lit 66000000000000000) Gram660ProofSharing.c507)

noncomputable def Gram660ProofSharing.c511 := (@HPow.hPow.{0, 0, 0} Complex Int Complex Gram660ProofSharing.c242 Gram660ProofSharing.c112 Gram660ProofSharing.c333)

noncomputable def Gram660ProofSharing.c512 := (@HMul.hMul.{0, 0, 0} Complex Complex Complex (@instHMul.{0} Complex Complex.instMul) Gram660ProofSharing.c330 Gram660ProofSharing.c511)

noncomputable def Gram660ProofSharing.c513 := (nat_lit 5942112188569825319515796275200000000000)

noncomputable def Gram660ProofSharing.c514 := (nat_lit 6307877850471822839406527784344423)

noncomputable def Gram660ProofSharing.c515 := (@HPow.hPow.{0, 0, 0} Complex Int Complex Gram660ProofSharing.c242 Gram660ProofSharing.c112 Gram660ProofSharing.c347)

noncomputable def Gram660ProofSharing.c516 := (@HMul.hMul.{0, 0, 0} Complex Complex Complex (@instHMul.{0} Complex Complex.instMul) Gram660ProofSharing.c344 Gram660ProofSharing.c515)

noncomputable def Gram660ProofSharing.c517 := (@Inv.inv.{0} Complex Complex.instInv Gram660ProofSharing.c115)

noncomputable def Gram660ProofSharing.c518 := (BSN.zpow_one_sub_two_mul Gram660ProofSharing.c112 (nat_lit 1) (nat_lit 1) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram660ProofSharing.c519 := (Enclosure.Complex.inv_re_eq_mul Gram660ProofSharing.c115)

noncomputable def Gram660ProofSharing.c520 := (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) (Gram660ProofSharing.c115 : ℂ).re (Gram660ProofSharing.c115 : ℂ).re)

noncomputable def Gram660ProofSharing.c521 := (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) (Gram660ProofSharing.c115 : ℂ).im (Gram660ProofSharing.c115 : ℂ).im)

noncomputable def Gram660ProofSharing.c522 := (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd) Gram660ProofSharing.c520 Gram660ProofSharing.c521)

noncomputable def Gram660ProofSharing.c523 := (Enclosure.Complex.normSq_eq_mul_add_mul Gram660ProofSharing.c115)

noncomputable def Gram660ProofSharing.c524 := (@Enclosure.Real.IsNear.mulLit_ff (Gram660ProofSharing.c115 : ℂ).re (Gram660ProofSharing.c115 : ℂ).re (nat_lit 100000) (nat_lit 400000) (nat_lit 0) (nat_lit 1) (nat_lit 100000) (nat_lit 400000) (nat_lit 0) (nat_lit 1) (nat_lit 1) (nat_lit 16) (nat_lit 0) (nat_lit 1) Gram660ProofSharing.c128 Gram660ProofSharing.c128 (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram660ProofSharing.c525 := (@Enclosure.Real.IsNear.mulLit_ff (Gram660ProofSharing.c115 : ℂ).im (Gram660ProofSharing.c115 : ℂ).im (nat_lit 203064874) (nat_lit 400000) (nat_lit 0) (nat_lit 1) (nat_lit 203064874) (nat_lit 400000) (nat_lit 0) (nat_lit 1) (nat_lit 10308835763158969) (nat_lit 40000000000) (nat_lit 0) (nat_lit 1) Gram660ProofSharing.c131 Gram660ProofSharing.c131 (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram660ProofSharing.c526 := (@Enclosure.Real.IsNear.addLit_ff Gram660ProofSharing.c520 Gram660ProofSharing.c521 (nat_lit 1) (nat_lit 16) (nat_lit 0) (nat_lit 1) (nat_lit 10308835763158969) (nat_lit 40000000000) (nat_lit 0) (nat_lit 1) (nat_lit 164941412210543504) (nat_lit 10308838263158969) (nat_lit 40000000000) (nat_lit 0) (nat_lit 1) Gram660ProofSharing.c524 Gram660ProofSharing.c525 (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram660ProofSharing.c527 := (@Neg.neg.{0} Real Real.instNeg (Gram660ProofSharing.c115 : ℂ).im)

noncomputable def Gram660ProofSharing.c528 := (Enclosure.Complex.inv_im_eq_mul Gram660ProofSharing.c115)

noncomputable def Gram660ProofSharing.c529 := (@Enclosure.Real.IsNear.neg (Gram660ProofSharing.c115 : ℂ).im Bool.false (nat_lit 203064874) (nat_lit 400000) (nat_lit 0) (nat_lit 1) Gram660ProofSharing.c131)

noncomputable def Gram660ProofSharing.c530 := (nat_lit 49517601571415210995964968960000000000)

noncomputable def Gram660ProofSharing.c531 := (nat_lit 18923633551415468518219583353033269)

noncomputable def Gram660ProofSharing.c532 := (nat_lit 2475880078570760549798248448000000000000000)

noncomputable def Gram660ProofSharing.c533 := (@Inv.inv.{0} Complex Complex.instInv Gram660ProofSharing.c113)

noncomputable def Gram660ProofSharing.c534 := (BSN.zpow_one_sub_two_mul Gram660ProofSharing.c112 (nat_lit 2) (nat_lit 3) (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram660ProofSharing.c535 := (Enclosure.Complex.inv_re_eq_mul Gram660ProofSharing.c113)

noncomputable def Gram660ProofSharing.c536 := (@Enclosure.Complex.IsNear.re_isNear Gram660ProofSharing.c113 Bool.true (nat_lit 30926504789476907) (nat_lit 160000000000) (nat_lit 0) (nat_lit 1) Bool.true (nat_lit 1046680456173007440977453) (nat_lit 8000000000000000) (nat_lit 0) (nat_lit 1) Zeta.Certificates.Gram.gp6_cert._proof_6)

noncomputable def Gram660ProofSharing.c537 := (nat_lit 1095542368456281184302448158257418600078554367209)

noncomputable def Gram660ProofSharing.c538 := (nat_lit 64000000000000000000000000000000)

noncomputable def Gram660ProofSharing.c539 := (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) (Gram660ProofSharing.c113 : ℂ).re (Gram660ProofSharing.c113 : ℂ).re)

noncomputable def Gram660ProofSharing.c540 := (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) (Gram660ProofSharing.c113 : ℂ).im (Gram660ProofSharing.c113 : ℂ).im)

noncomputable def Gram660ProofSharing.c541 := (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd) Gram660ProofSharing.c539 Gram660ProofSharing.c540)

noncomputable def Gram660ProofSharing.c542 := (Enclosure.Complex.normSq_eq_mul_add_mul Gram660ProofSharing.c113)

noncomputable def Gram660ProofSharing.c543 := (nat_lit 956448698493538067760042686286649)

noncomputable def Gram660ProofSharing.c544 := (nat_lit 1095539977334534950457278758150702883456054367209)

noncomputable def Gram660ProofSharing.c545 := (nat_lit 28045884632480798318142672851389916162010991800550400000000000000000000)

noncomputable def Gram660ProofSharing.c546 := (@Enclosure.Real.IsNear.mulLit_tt (Gram660ProofSharing.c113 : ℂ).re (Gram660ProofSharing.c113 : ℂ).re (nat_lit 30926504789476907) (nat_lit 160000000000) (nat_lit 0) (nat_lit 1) (nat_lit 30926504789476907) (nat_lit 160000000000) (nat_lit 0) (nat_lit 1) Gram660ProofSharing.c543 (nat_lit 25600000000000000000000) (nat_lit 0) (nat_lit 1) Gram660ProofSharing.c536 Gram660ProofSharing.c536 (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram660ProofSharing.c547 := (@Enclosure.Complex.IsNear.im_isNear Gram660ProofSharing.c113 Bool.true (nat_lit 30926504789476907) (nat_lit 160000000000) (nat_lit 0) (nat_lit 1) Bool.true (nat_lit 1046680456173007440977453) (nat_lit 8000000000000000) (nat_lit 0) (nat_lit 1) Zeta.Certificates.Gram.gp6_cert._proof_6)

noncomputable def Gram660ProofSharing.c548 := (@Enclosure.Real.IsNear.mulLit_tt (Gram660ProofSharing.c113 : ℂ).im (Gram660ProofSharing.c113 : ℂ).im (nat_lit 1046680456173007440977453) (nat_lit 8000000000000000) (nat_lit 0) (nat_lit 1) (nat_lit 1046680456173007440977453) (nat_lit 8000000000000000) (nat_lit 0) (nat_lit 1) Gram660ProofSharing.c544 Gram660ProofSharing.c538 (nat_lit 0) (nat_lit 1) Gram660ProofSharing.c547 Gram660ProofSharing.c547 (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram660ProofSharing.c549 := (@Enclosure.Real.IsNear.addLit_ff Gram660ProofSharing.c539 Gram660ProofSharing.c540 Gram660ProofSharing.c543 (nat_lit 25600000000000000000000) (nat_lit 0) (nat_lit 1) Gram660ProofSharing.c544 Gram660ProofSharing.c538 (nat_lit 0) (nat_lit 1) Gram660ProofSharing.c545 Gram660ProofSharing.c537 Gram660ProofSharing.c538 (nat_lit 0) (nat_lit 1) Gram660ProofSharing.c546 Gram660ProofSharing.c548 (@Eq.refl.{1} Bool Bool.true) (@Eq.refl.{1} Bool Bool.true))

noncomputable def Gram660ProofSharing.c550 := (@Neg.neg.{0} Real Real.instNeg (Gram660ProofSharing.c113 : ℂ).im)

noncomputable def Gram660ProofSharing.c551 := (Enclosure.Complex.inv_im_eq_mul Gram660ProofSharing.c113)

noncomputable def Gram660ProofSharing.c552 := (@Enclosure.Real.IsNear.neg (Gram660ProofSharing.c113 : ℂ).im Bool.true (nat_lit 1046680456173007440977453) (nat_lit 8000000000000000) (nat_lit 0) (nat_lit 1) Gram660ProofSharing.c547)

noncomputable def Gram660ProofSharing.c553 := (BSN.logSumC Gram660ProofSharing.c107 (nat_lit 0))

noncomputable def Gram660ProofSharing.c554 := (Enclosure.sfrac Bool.false (nat_lit 98304000000000000000000000) Gram660ProofSharing.c144)


