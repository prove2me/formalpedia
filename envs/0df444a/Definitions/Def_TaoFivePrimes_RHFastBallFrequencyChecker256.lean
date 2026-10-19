-- Prove2me | Definitions.Def_TaoFivePrimes_RHFastBallFrequencyChecker256
-- name    : TaoFivePrimes_RHFastBallFrequencyChecker256
-- status  : Definition
-- author  : @raresbuhai
-- created : 2026-10-16T10:31:30.377335+00:00
-- url     : https://prove2.me/theorems/2a1968b5-a952-4e6d-a8a2-0addb17c7370
-- title:
--   Full-frequency256-bit Fourier certificate checker
-- statement:
--   The full-frequency256-bit ball checker validates52 Hermite terms, a40-step exponential Horner chain,20 squarings and24 output budgets. Arithmetic validation and analytic soundness are separate proofs.
-- source:
--   Platt DOI10.1090/mcom/3198. Original surrounding attribution sometik179 c9908072-d99a-4431-aad8-a72c6352619a and Gabewhigham.

import Definitions.Def_TaoFivePrimes_RHFastComplexBallArithmetic
namespace RHFastBallFrequencyChecker256
open RHFastBallArithmetic
noncomputable def D : Nat := 2^256
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
 decide ((a.re-p.1*(2:Int)^171).natAbs+(a.im-p.2*(2:Int)^171).natAbs+a.radius≤D/(2*10^15))
noncomputable def valid (j:Nat) (anchor pi root omega:Ball)
 (qs factors hs es ss:List Ball) (reference:List (Int×Int)) : Bool :=
 let nu:=frequency pi omega j
 let p:=pnu nu
 let x:=gaussianInput nu
 let z:=divide x (2^20)
 let c:=common anchor root (entry ss 20)
 decide (qs.length=29 ∧ factors.length=24 ∧ hs.length=52 ∧ es.length=41 ∧ ss.length=21 ∧ reference.length=24) &&
 decide (magnitude nu+nu.radius≤300*D ∧ magnitude x+x.radius≤65536*D) &&
 decide (entry hs 0=integer D 1 ∧ entry hs 1=p ∧ entry es 0=integer D 1 ∧ entry ss 0=inflate (entry es 40) 1) &&
 (List.range 50).all (fun n=>decide (entry hs (n+2)=hermiteStep p n (entry hs n) (entry hs (n+1)))) &&
 (List.range 40).all (fun n=>decide (entry es (n+1)=expStep z n (entry es n))) &&
 (List.range 20).all (fun n=>decide (entry ss (n+1)=mul D (entry ss n) (entry ss n))) &&
 (List.range 24).all (fun k=>budget (output c qs factors hs k) ((reference[k]?).getD (0,0)))
end RHFastBallFrequencyChecker256
noncomputable def TaoFivePrimes_RHFastBallFrequencyChecker256 : Nat := 24


