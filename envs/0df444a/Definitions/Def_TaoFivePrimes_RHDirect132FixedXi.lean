-- Prove2me | Definitions.Def_TaoFivePrimes_RHDirect132FixedXi
-- name    : TaoFivePrimes_RHDirect132FixedXi
-- status  : Definition
-- author  : @Johan Mercedes
-- created : 2026-10-28T00:51:57.12772+00:00
-- url     : https://prove2.me/theorems/c8267184-0adf-40fe-bb75-f7a54ec2dca0
-- title:
--   Fixed-point candidate xi coefficients at height 132
-- statement:
--   Use the stored parity-selected fixed-point components to define candidate completed-zeta coefficients and the resulting scaled xi coefficients at $1/2+132i$. The complex expression and a parity-based rational expression are defined separately. Also define the proposed inequality between the rational candidate and the stored rounded coefficient, leaving a margin of $10^{-43}$. These are definitions; equality and inequalities are separate certificates.
-- source:
--   Exact arithmetic built on the theta/Mellin and finite quadrature framework of Gabewhigham and sometik179.

/- Candidate xi coefficients formed from the fixed-point rule components.
The data alone assert no approximation, rounding inequality, or zero result. -/
import Definitions.Def_TaoFivePrimes_RHDirect132FastNumerator
import Definitions.Def_TaoFivePrimes_RH132RoundedCoefficients14
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Rat.Cast.Defs
set_option autoImplicit false

namespace RHDirect132FixedXi

def lambdaQ (n : ℕ) : ℚ :=
  (RHDirect132FastNumerator.fixed n:ℚ)/((10^90:ℚ)*2^n)

noncomputable def lambdaC (n : ℕ) : ℂ :=
  if n%2=0 then (lambdaQ n:ℂ) else Complex.I*(lambdaQ n:ℂ)

noncomputable def xiC (n : ℕ) : ℂ :=
  (10^43:ℂ)*Complex.I^n*((if n=0 then (1/2:ℂ) else 0) +
    (-(69697/8:ℂ))*lambdaC n +
    (if 1≤n then Complex.I*(132:ℂ)*lambdaC (n-1) else 0) +
    (if 2≤n then (1/2:ℂ)*lambdaC (n-2) else 0))

def xiQ (n : ℕ) : ℚ :=
  (10^43:ℚ) *
  if n%2=0 then
    (-1:ℚ)^(n/2)*((if n=0 then (1/2:ℚ) else 0) -
      (69697/8:ℚ)*lambdaQ n - (if 1≤n then (132:ℚ)*lambdaQ (n-1) else 0) +
      (if 2≤n then (1/2:ℚ)*lambdaQ (n-2) else 0))
  else
    (-1:ℚ)^((n+1)/2)*(-(69697/8:ℚ)*lambdaQ n +
      (if 1≤n then (132:ℚ)*lambdaQ (n-1) else 0) +
      (if 2≤n then (1/2:ℚ)*lambdaQ (n-2) else 0))

def targetQ (n : ℕ) : ℚ :=
  (TaoFivePrimes_RH132RoundedCoefficients14.getD n 0:ℚ)/10^14

def boundQ (n : ℕ) : ℚ :=
  if n<23 then 1/10^14 else if n<26 then 1/10^15
  else if n<30 then 1/10^19 else if n<35 then 1/10^23
  else if n<40 then 1/10^30 else 1/10^37

def roundingHolds (n : ℕ) : Prop :=
  |xiQ n-targetQ n| + 1/10^43 ≤ boundQ n

end RHDirect132FixedXi


