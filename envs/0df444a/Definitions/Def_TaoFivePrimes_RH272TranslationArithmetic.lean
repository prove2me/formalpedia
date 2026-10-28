-- Prove2me | Definitions.Def_TaoFivePrimes_RH272TranslationArithmetic
-- name    : TaoFivePrimes_RH272TranslationArithmetic
-- status  : Definition
-- author  : @Johan Mercedes
-- created : 2026-10-27T19:18:16.428235+00:00
-- url     : https://prove2.me/theorems/241658ca-1f1b-4316-b0a7-636fd4ef5896
-- title:
--   Integer translation of 272 Mellin moment candidates
-- statement:
--   For a scaled center parameter $p$, a normalization $S$, and a nonnegative index $n$, this definition forms an integer $N_{p,S,n}$ and a positive integer $D$ by exact binomial translation of the 272 proposed moment numerators.
--
--   $$
--   (p,S,n)\longmapsto N_{p,S,n}/D.
--   $$
--
--   The expression is an arithmetic model. It asserts neither the accuracy of the candidate moments nor an analytic xi approximation.
-- source:
--   Exact integer translation of the published 256 moment data and 16 extended candidate moments, using the local xi/Taylor framework of sometik179, Prove2Me c9908072-d99a-4431-aad8-a72c6352619a, https://prove2.me/submissions/c9908072-d99a-4431-aad8-a72c6352619a; theta/Mellin foundations by Gabewhigham. The height-110.5 arithmetic data are new.

/- Exact integer translation of the 272 proposed Mellin moments. The
original 256-moment data and xi translation framework are by sometik179,
with theta/Mellin foundations by Gabewhigham. This is arithmetic data only. -/
import Definitions.Def_TaoFivePrimes_RH14To100MomentModel
import Definitions.Def_TaoFivePrimes_RHExtendedMomentData256to271
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
set_option autoImplicit false
open Finset

namespace RH272TranslationArithmetic

noncomputable def denominator : ℕ := 8*10^64*2^4352

noncomputable def momentInteger (j : ℕ) : ℤ :=
  if j<256 then TaoFivePrimes_RH14To100RoundedMomentData.getD j 0
  else TaoFivePrimes_RHExtendedMomentData256to271.getD (j-256) 0

noncomputable def chooseFast (k n : ℕ) : ℕ :=
  if n≤k then k.factorial/(n.factorial*(k-n).factorial) else 0

noncomputable def numerator (p : ℤ) (S n : ℕ) : ℤ :=
  (if n=0 then (4*10^64*2^4352:ℤ) else 0)*(S:ℤ)-
  (S:ℤ)*∑ j ∈ range 272,
    momentInteger j*(-1:ℤ)^j*((2^(4352-16*j+n):ℕ):ℤ)*
    ((chooseFast (2*j+2) n:ℤ)*p^(2*j+2-n)+
      (chooseFast (2*j) n:ℤ)*p^(2*j-n))

end RH272TranslationArithmetic


