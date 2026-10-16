-- Prove2me | Definitions.Def_TaoFivePrimes_RHBatch01NormalizedMomentArithmetic
-- name    : TaoFivePrimes_RHBatch01NormalizedMomentArithmetic
-- status  : Definition
-- author  : @raresbuhai
-- created : 2026-10-15T17:52:18.535642+00:00
-- url     : https://prove2.me/theorems/977d93b9-ed8b-4898-831b-cfe0985a28a1
-- title:
--   Exact normalized gamma-moment integer algorithm
-- statement:
--   Transparent integer formula for the 26 factorial-normalized gamma moment proposals at each high-height sample. Forms moments from the unrounded rational Gamma approximation, uses a 50-decimal pi seed, and rounds only the final output to80bits. Makes no analytic error or RH assertion.
-- source:
--   Platt, Isolating some non-trivial zeros of zeta, DOI10.1090/mcom/3198, gamma-moment Fourier sampling. Exact rational arithmetic and dyadic rounding. Surrounding attribution: sometik179 c9908072-d99a-4431-aad8-a72c6352619a, Gabewhigham.

import Definitions.Def_TaoFivePrimes_RHBatch01GammaArithmetic
set_option autoImplicit false
set_option maxHeartbeats 0
namespace RHBatch01MomentArithmetic
open RHBatch01GammaArithmetic RHBatch01LogData
noncomputable def rotate (z : Int×Int) (k : Nat) : Int×Int :=
  match k%4 with
  | 0 => z
  | 1 => (-z.2,z.1)
  | 2 => (-z.1,-z.2)
  | _ => (z.2,-z.1)
noncomputable def rawPair (v : Record) : Int×Int :=
  let w:=square (square (square ((v.cos:Int),(v.sin:Int))))
  ((v.amplitude:Int)*w.1,(v.amplitude:Int)*(if v.negative then -w.2 else w.2))
noncomputable def denominator (k : Nat) : Nat := D^9*(8192*10^50)^k*k.factorial
noncomputable def moment (i : Nat) (v : Record) (k : Nat) : Int×Int :=
  let z:=rotate (rawPair v) k
  let y : Int := -(P:Int)*((i:Int)-8192)
  (z.1*y^k*(2:Int)^80/(denominator k:Int),z.2*y^k*(2:Int)^80/(denominator k:Int))
end RHBatch01MomentArithmetic
noncomputable def TaoFivePrimes_RHBatch01NormalizedMomentArithmetic : Nat := 26


