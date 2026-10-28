-- Prove2me | Definitions.Def_TaoFivePrimes_RHExtendedMomentCorrelationCache
-- name    : TaoFivePrimes_RHExtendedMomentCorrelationCache
-- status  : Definition
-- author  : @Johan Mercedes
-- created : 2026-10-27T19:11:12.348387+00:00
-- url     : https://prove2.me/theorems/edd7603d-6cf4-4d95-b970-e0aed0d37782
-- title:
--   Lookup of cached theta-jet correlations
-- statement:
--   For panel index $i$ and correlation index $m$, this definition looks up a proposed integer $B_{i,m}$ in four stored correlation tables. Entries outside the stored ranges default to zero.
--
--   $$
--   (i,m)\longmapsto B_{i,m}.
--   $$
--
--   The lookup is reusable across moment orders; correctness of the entries is established separately.
-- source:
--   Derived here from the exact theta-jet and Mellin quadrature framework of sometik179, Prove2Me c9908072-d99a-4431-aad8-a72c6352619a, https://prove2.me/submissions/c9908072-d99a-4431-aad8-a72c6352619a; theta/Mellin foundations by Gabewhigham.

/- Lookup interface for the four proposed integer correlation tables.
The tables derive from the theta-jet data of sometik179 and Gabewhigham.
No exact equality is asserted without the separate finite certificates. -/
import Definitions.Def_TaoFivePrimes_RHExtendedMomentCorrelations0
import Definitions.Def_TaoFivePrimes_RHExtendedMomentCorrelations1
import Definitions.Def_TaoFivePrimes_RHExtendedMomentCorrelations2
import Definitions.Def_TaoFivePrimes_RHExtendedMomentCorrelations3
set_option autoImplicit false

noncomputable def TaoFivePrimes_RHExtendedMomentCorrelationCache (i m : ℕ) : ℤ :=
  let row := if i<4 then TaoFivePrimes_RHExtendedMomentCorrelations0.getD i []
    else if i<8 then TaoFivePrimes_RHExtendedMomentCorrelations1.getD (i-4) []
    else if i<12 then TaoFivePrimes_RHExtendedMomentCorrelations2.getD (i-8) []
    else if i<16 then TaoFivePrimes_RHExtendedMomentCorrelations3.getD (i-12) []
    else []
  row.getD m 0


