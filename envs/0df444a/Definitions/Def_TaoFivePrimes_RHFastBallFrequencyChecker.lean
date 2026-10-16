-- Prove2me | Definitions.Def_TaoFivePrimes_RHFastBallFrequencyChecker
-- name    : TaoFivePrimes_RHFastBallFrequencyChecker
-- status  : Definition
-- author  : @raresbuhai
-- created : 2026-10-16T09:48:27.131722+00:00
-- url     : https://prove2.me/theorems/c4fc67f6-d248-4ed6-8a37-8e917cf9dbe1
-- title:
--   Integer certificate checker for a short Fourier formula
-- statement:
--   Pure integer checker for cached Horner, Gaussian squaring and scaled Hermite recurrences at one Fourier frequency, followed by24 short dot products and an outward error-budget comparison. This Boolean alone does not establish seed accuracy, analytic soundness or an RH window.
-- source:
--   Integer ball evaluation for the center Gaussian/Hermite method, Platt DOI10.1090/mcom/3198. Original surrounding attribution sometik179 c9908072-d99a-4431-aad8-a72c6352619a and Gabewhigham.

import Definitions.Def_TaoFivePrimes_RHFastComplexBallArithmetic
namespace RHFastBallFrequencyChecker
open RHFastBallArithmetic
noncomputable def D : Nat := 2^128
noncomputable def entry (xs:List Ball) (n:Nat) : Ball := (xs[n]?).getD zero
noncomputable def frequency (pi omega:Ball) (j:Nat) : Ball :=
 scale (sub (divide (scale pi ((2*j:Nat):Int)) 512) omega) 20
noncomputable def pnu (nu:Ball) : Ball := mul D nu (rational D 5 64)
noncomputable def hermiteStep (p:Ball) (n:Nat) (a b:Ball) : Ball :=
 sub (mul D p b) (mul D (rational D (((n+1)*25:Nat):Int) 4096) a)
noncomputable def gaussianInput (nu:Ball) : Ball := neg (divide (mul D nu nu) 2)
noncomputable def expStep (z:Ball) (n:Nat) (a:Ball) : Ball :=
 add (integer D 1) (divide (mul D z a) (40-n))
noncomputable def dot (as bs:List Ball) : Ball :=
 (as.zip bs).foldl (fun a p=>add a (mul D p.1 p.2)) zero
noncomputable def rotated (qs:List Ball) : List Ball :=
 qs.zipIdx.map (fun p=>rotate p.1 p.2)
noncomputable def common (anchor root exp:Ball) : Ball :=
 mul D (mul D anchor (scale root 20)) exp
noncomputable def output (c:Ball) (qs factors hs:List Ball) (k:Nat) : Ball :=
 mul D (mul D c (entry factors k)) (dot (rotated qs) (hs.drop k))
noncomputable def budget (a:Ball) (p:Int×Int) : Bool :=
 decide ((a.re-p.1*(2:Int)^43).natAbs+(a.im-p.2*(2:Int)^43).natAbs+a.radius≤D/(2*10^15))
noncomputable def valid (j:Nat) (anchor pi root omega:Ball)
 (qs factors hs es ss:List Ball) (reference:List (Int×Int)) : Bool :=
 let nu:=frequency pi omega j
 let p:=pnu nu
 let x:=gaussianInput nu
 let z:=divide x 1024
 let c:=common anchor root (entry ss 10)
 decide (qs.length=29 ∧ factors.length=24 ∧ hs.length=52 ∧ es.length=41 ∧ ss.length=11 ∧ reference.length=24) &&
 decide (magnitude nu+nu.radius≤33*D ∧ magnitude x+x.radius≤1024*D) &&
 decide (entry hs 0=integer D 1 ∧ entry hs 1=p ∧ entry es 0=integer D 1 ∧ entry ss 0=inflate (entry es 40) 1) &&
 (List.range 50).all (fun n=>decide (entry hs (n+2)=hermiteStep p n (entry hs n) (entry hs (n+1)))) &&
 (List.range 40).all (fun n=>decide (entry es (n+1)=expStep z n (entry es n))) &&
 (List.range 10).all (fun n=>decide (entry ss (n+1)=mul D (entry ss n) (entry ss n))) &&
 (List.range 24).all (fun k=>budget (output c qs factors hs k) ((reference[k]?).getD (0,0)))
end RHFastBallFrequencyChecker
noncomputable def TaoFivePrimes_RHFastBallFrequencyChecker : Nat := 24


