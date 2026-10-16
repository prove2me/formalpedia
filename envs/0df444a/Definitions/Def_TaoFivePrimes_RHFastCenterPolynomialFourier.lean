-- Prove2me | Definitions.Def_TaoFivePrimes_RHFastCenterPolynomialFourier
-- name    : TaoFivePrimes_RHFastCenterPolynomialFourier
-- status  : Definition
-- author  : @raresbuhai
-- created : 2026-10-16T09:03:44.479426+00:00
-- url     : https://prove2.me/theorems/b58ec157-8b19-40ef-bbe9-5cf02063d606
-- title:
--   Center polynomial and short Gaussian Fourier formula
-- statement:
--   The degree28 center-polynomial Gamma proxy and its short Gaussian/Hermite Fourier formula. The polynomial coordinate is t/256. The anchor uses the parameterized integer Gamma program at the center only. Definitions alone assert no approximation bound, Fourier identity, certified table or RH window.
-- source:
--   Platt, Isolating some non-trivial zeros of zeta, DOI10.1090/mcom/3198; Gaussian/Hermite transform and center expansion of the Stirling exponent. Original surrounding attribution: sometik179 c9908072-d99a-4431-aad8-a72c6352619a and Gabewhigham.

import Mathlib
import Definitions.Def_TaoFivePrimes_RHFastKernelGammaArithmetic
set_option autoImplicit false
namespace RHFastCenterPolynomial
open Complex Finset Polynomial
noncomputable def omega (T:Nat) : ℝ :=
 Real.log ((T:ℝ)/2)/2-1/(48*(T:ℝ)^2)
noncomputable def center (T:Nat) : ℂ := 1/4+(((T:ℝ)/2:ℝ):ℂ)*I
noncomputable def anchor (T:Nat) : ℂ :=
 let a:=RHFastKernelGammaArithmetic.compute T 8192
 let q:ℂ:=((a.cos:ℂ)+(a.sin:ℂ)*I)/(RHFastKernelLogData.D:ℂ)
 let phase:ℂ:=if a.negative then starRingEnd ℂ q else q
 ((a.amplitude:ℂ)/(RHFastKernelLogData.D:ℂ))*phase^8
noncomputable def delta (T:Nat) (t:ℝ) : ℂ :=
 let v:=center T
 let u:ℂ:=((t/2:ℝ):ℂ)*I
 u*(Complex.log v-1)+(v+u-1/2)*Complex.logTaylor 7 (u/v)+
 (1/(12*v))*((∑j∈Finset.range 7,(-u/v)^j)-1)+
 ((Real.pi*t/4:ℝ):ℂ)-I*(omega T:ℂ)*t
noncomputable def carrier (T:Nat) (t:ℝ) : ℂ :=
 Complex.exp (((-t^2/800:ℝ):ℂ)+I*(omega T:ℂ)*t)
noncomputable def exponentialPolynomial (d:ℂ) : ℂ :=
 ∑r∈Finset.range 5,d^r/(r.factorial:ℂ)
noncomputable def proxy (T:Nat) (t:ℝ) : ℂ :=
 anchor T*carrier T t*exponentialPolynomial (delta T t)
noncomputable def momentFactor (k:Nat) (t:ℝ) : ℂ :=
 (-2*(Real.pi:ℂ)*I*(t:ℂ))^k/((k.factorial:ℂ)*(512:ℂ)^k)
noncomputable def momentProxy (T k:Nat) (t:ℝ) : ℂ :=
 proxy T t*momentFactor k t
-- The polynomial variable is the scaled coordinate x=t/256.
noncomputable def deltaPolynomial (T:Nat) : Polynomial ℂ :=
 let v:=center T
 let u:Polynomial ℂ:=C (128*I)*X
 let s:Polynomial ℂ:=u*C v⁻¹
 u*C (Complex.log v-1)+(C (v-1/2)+u)*
   (∑j∈Finset.range 7,C ((-1:ℂ)^(j+1)/(j:ℂ))*s^j)+
 C (1/(12*v))*((∑j∈Finset.range 7,(-s)^j)-1)+
 C ((64*Real.pi:ℂ)-256*I*(omega T:ℂ))*X
noncomputable def proxyPolynomial (T:Nat) : Polynomial ℂ :=
 ∑r∈Finset.range 5,(deltaPolynomial T)^r*C ((r.factorial:ℂ)⁻¹)
noncomputable def scaledHermite (n:Nat) (x:ℝ) : ℝ :=
 (5/64:ℝ)^n*(Polynomial.hermite n).eval₂ (Int.castRingHom ℝ) x
noncomputable def frequency (T:Nat) (x:ℝ) : ℝ :=20*(2*Real.pi*x-omega T)
noncomputable def fourierFormula (T k:Nat) (x:ℝ) : ℂ :=
 let ν:=frequency T x
 anchor T*(20:ℂ)*((Real.sqrt (2*Real.pi)*Real.exp (-ν^2/2):ℝ):ℂ)*
   (((-Real.pi:ℝ):ℂ)^k/(k.factorial:ℂ))*
   (∑d∈Finset.range 29,(proxyPolynomial T).coeff d*(-I)^d*
       ((scaledHermite (d+k) ν:ℝ):ℂ))
end RHFastCenterPolynomial
noncomputable def TaoFivePrimes_RHFastCenterPolynomialFourier : Nat := 28


