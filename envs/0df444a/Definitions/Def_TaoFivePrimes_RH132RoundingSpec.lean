-- Prove2me | Definitions.Def_TaoFivePrimes_RH132RoundingSpec
-- name    : TaoFivePrimes_RH132RoundingSpec
-- status  : Definition
-- author  : @Johan Mercedes
-- created : 2026-10-28T00:12:24.980024+00:00
-- url     : https://prove2.me/theorems/c6628349-362d-47c2-a989-15ae54897fda
-- title:
--   Proposed rounding bounds for height-132 xi coefficients
-- statement:
--   For the stored forty candidate polynomial numerators, define $p_n=c_n/10^{14}$ for $n<40$ and $p_n=0$ for $n\ge40$. Define the proposed tolerance
--
--   $$
--   \varepsilon_n=
--   \begin{cases}
--   10^{-14},&n<23,\\
--   10^{-15},&23\le n<26,\\
--   10^{-19},&26\le n<30,\\
--   10^{-23},&30\le n<35,\\
--   10^{-30},&35\le n<40,\\
--   10^{-37},&n\ge40.
--   \end{cases}
--   $$
--
--   This is a specification of candidate values and bounds; it asserts no enclosure.
-- source:
--   Exact fixed-point oscillatory quadrature built on the theta/Mellin framework due to Gabewhigham and sometik179.

/- Candidate numerical rounding targets for the height-132 local xi polynomial.
The theta/Mellin framework is due to Gabewhigham and sometik179. The bounds
below are a specification, not a claim that any candidate is enclosed. -/
import Definitions.Def_TaoFivePrimes_RH132RoundedCoefficients14
import Definitions.Def_TaoFivePrimes_RHDirect132XiCoefficients
import Mathlib.Data.Real.Basic

set_option autoImplicit false

namespace RH132RoundingSpec

noncomputable def proposed (n : ℕ) : ℝ :=
  (TaoFivePrimes_RH132RoundedCoefficients14.getD n 0:ℝ)/(10^14:ℝ)

noncomputable def bound (n : ℕ) : ℝ :=
  if n<23 then 1/10^14 else if n<26 then 1/10^15
  else if n<30 then 1/10^19 else if n<35 then 1/10^23
  else if n<40 then 1/10^30 else 1/10^37

end RH132RoundingSpec


