-- Prove2me | Definitions.Def_TaoFivePrimes_RH304TranslationArithmetic
-- name    : TaoFivePrimes_RH304TranslationArithmetic
-- status  : Definition
-- author  : @Johan Mercedes
-- created : 2026-10-27T19:50:51.732994+00:00
-- url     : https://prove2.me/theorems/46013d23-bd8d-45ce-bf26-c8e5fe2c9243
-- title:
--   Integer translation of 304 Mellin moment candidates
-- statement:
--   For a scaled center parameter $p$, a normalization $S$, and a nonnegative index $n$, this definition forms an integer $N_{p,S,n}$ and a positive integer $D$ by exact binomial translation of the 304 proposed moment numerators.
--
--   $$
--   (p,S,n)\longmapsto N_{p,S,n}/D.
--   $$
--
--   The expression is an arithmetic model. It asserts neither the accuracy of the candidate moments nor an analytic xi approximation.
-- source:
--   Exact integer translation of the published 256 moment data and 48 extended candidate moments, using the local xi/Taylor framework of sometik179, Prove2Me c9908072-d99a-4431-aad8-a72c6352619a, https://prove2.me/submissions/c9908072-d99a-4431-aad8-a72c6352619a; theta/Mellin foundations by Gabewhigham. The height-114.5 arithmetic data are new.

/- Exact integer translation of the 304 proposed Mellin moments. The
original 256-moment data and xi translation framework are by sometik179,
with theta/Mellin foundations by Gabewhigham. This is arithmetic data only. -/
import Definitions.Def_TaoFivePrimes_RH14To100MomentModel
import Definitions.Def_TaoFivePrimes_RH272TranslationArithmetic
import Definitions.Def_TaoFivePrimes_RHExtendedMomentData272to303
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
set_option autoImplicit false
open Finset

namespace RH304TranslationArithmetic

noncomputable def denominator : ℕ := 8*10^64*2^4864

noncomputable def momentInteger (j : ℕ) : ℤ :=
  if j<272 then RH272TranslationArithmetic.momentInteger j
  else TaoFivePrimes_RHExtendedMomentData272to303.getD (j-272) 0

noncomputable def chooseFast (k n : ℕ) : ℕ :=
  if n≤k then k.factorial/(n.factorial*(k-n).factorial) else 0

noncomputable def numerator (p : ℤ) (S n : ℕ) : ℤ :=
  (if n=0 then (4*10^64*2^4864:ℤ) else 0)*(S:ℤ)-
  (S:ℤ)*∑ j ∈ range 304,
    momentInteger j*(-1:ℤ)^j*((2^(4864-16*j+n):ℕ):ℤ)*
    ((chooseFast (2*j+2) n:ℤ)*p^(2*j+2-n)+
      (chooseFast (2*j) n:ℤ)*p^(2*j-n))

end RH304TranslationArithmetic


