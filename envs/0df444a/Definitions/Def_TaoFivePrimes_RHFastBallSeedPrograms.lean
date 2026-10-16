-- Prove2me | Definitions.Def_TaoFivePrimes_RHFastBallSeedPrograms
-- name    : TaoFivePrimes_RHFastBallSeedPrograms
-- status  : Definition
-- author  : @raresbuhai
-- created : 2026-10-16T10:03:36.77472+00:00
-- url     : https://prove2.me/theorems/a53d6cf8-6994-4f79-b2a1-6c23fe4516bb
-- title:
--   Integer center seed programs for the short Fourier method
-- statement:
--   Ordinary integer error-ball programs for pi, sqrt(2pi),64-term odd logarithm Horner evaluation, the carrier frequency, complex center and inverse, degree4 small-log correction and the single Gamma anchor. Analytic containment and concrete evaluations require separate proofs.
-- source:
--   Fixed-point seed evaluation for the center Gaussian/Hermite method; Platt DOI10.1090/mcom/3198. Original surrounding attribution sometik179 c9908072-d99a-4431-aad8-a72c6352619a and Gabewhigham.

import Definitions.Def_TaoFivePrimes_RHFastComplexBallArithmetic
namespace RHFastBallSeedPrograms
open RHFastBallArithmetic
noncomputable def D:Nat:=2^128
noncomputable def Q:Nat:=2*10^20
noncomputable def pi : Ball := inflate (rational D 628318530717958647693 Q) (D/Q+1)
noncomputable def root : Ball := inflate (rational D 501325654926200100483 Q) (D/Q+1)
noncomputable def horner (D:Nat) (x:Ball) (m:Nat) : Nat→Ball
 |0=>zero
 |1=>rational D 1 (2*m+1)
 |n+2=>add (rational D 1 (2*m+1)) (mul D x (horner D x (m+1) (n+1)))
noncomputable def logRatio (n d:Nat) : Ball :=
 let x:=rational D ((n:Int)-(d:Int)) (n+d)
 let u:=horner D (mul D x x) 0 64
 inflate (scale (mul D x u) 2) 1
noncomputable def logb (T:Nat) : Ball := add (scale (logRatio 2 1) 30) (logRatio T (2^31))
noncomputable def omega (T:Nat) : Ball := sub (divide (logb T) 2) (rational D 1 (48*T*T))
noncomputable def center (T:Nat) : Ball := add (rational D 1 4) (rotate (rational D (T:Int) 2) 3)
noncomputable def inverseCenter (T:Nat) : Ball :=
 add (rational D 4 (1+4*T*T)) (rotate (rational D (-(8*(T:Int))) (1+4*T*T)) 3)
noncomputable def small (T:Nat) : Ball := rotate (rational D (-1) (2*T)) 3
noncomputable def logSmall (T:Nat) : Ball :=
 inflate ((List.range 4).foldl (fun u r=>add u
  (divide (scale (power D (small T) (r+1)) ((-1:Int)^(r+2))) (r+1))) zero) 1
noncomputable def logCenter (T:Nat) : Ball :=
 add (add (logb T) (rotate (divide pi 2) 3)) (logSmall T)
noncomputable def anchor (cos sin amplitude:Int) (negative:Bool) : Ball :=
 let q:Ball:=⟨cos,(if negative then -sin else sin),0⟩
 mul D (⟨amplitude,0,0⟩:Ball) (power D q 8)
end RHFastBallSeedPrograms
noncomputable def TaoFivePrimes_RHFastBallSeedPrograms : Nat := 128


