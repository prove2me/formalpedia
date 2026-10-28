-- Prove2me | Definitions.Def_TaoFivePrimes_RH320TranslationArithmetic
-- name    : TaoFivePrimes_RH320TranslationArithmetic
-- status  : Definition
-- author  : @Johan Mercedes
-- created : 2026-10-27T22:34:56.062359+00:00
-- url     : https://prove2.me/theorems/d67f82bd-c884-41ce-8b3a-f60cb77c21ae
-- title:
--   Exact integer translation of 320 Mellin moment candidates
-- statement:
--   This module defines a common denominator, integer moment numerators, and an exact binomial translation numerator for 320 candidate Mellin moments. It is an arithmetic data interface; it does not assert an approximation to the Riemann xi function.
-- source:
--   Exact translation of candidate Mellin moment data for the height-123 xi polynomial. The earlier theta-jet and Mellin framework is due to sometik179 and Gabewhigham; the additional rounded data and translation certificates are new.

/- Exact integer translation of 320 proposed Mellin moments. The original
moment data and xi translation framework are due to sometik179, with
theta/Mellin foundations by Gabewhigham. This definition is arithmetic data. -/
import Definitions.Def_TaoFivePrimes_RH304TranslationArithmetic
import Definitions.Def_TaoFivePrimes_RHExtendedMomentData304to319
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
set_option autoImplicit false
open Finset

namespace RH320TranslationArithmetic

noncomputable def denominator : ℕ := 8*10^64*2^5120

noncomputable def momentInteger (j : ℕ) : ℤ :=
  if j<304 then RH304TranslationArithmetic.momentInteger j
  else TaoFivePrimes_RHExtendedMomentData304to319.getD (j-304) 0

noncomputable def chooseFast (k n : ℕ) : ℕ :=
  if n≤k then k.factorial/(n.factorial*(k-n).factorial) else 0

noncomputable def numerator (p : ℤ) (S n : ℕ) : ℤ :=
  (if n=0 then (4*10^64*2^5120:ℤ) else 0)*(S:ℤ)-
  (S:ℤ)*∑ j ∈ range 320,
    momentInteger j*(-1:ℤ)^j*((2^(5120-16*j+n):ℕ):ℤ)*
    ((chooseFast (2*j+2) n:ℤ)*p^(2*j+2-n)+
      (chooseFast (2*j) n:ℤ)*p^(2*j-n))

end RH320TranslationArithmetic


