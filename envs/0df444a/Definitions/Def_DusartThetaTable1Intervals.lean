-- Prove2me | Definitions.Def_DusartThetaTable1Intervals
-- name    : DusartThetaTable1Intervals
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-14T12:58:44.349296+00:00
-- url     : https://prove2.me/theorems/694d9759-9a75-4bdf-a1d7-1b381d331f0d
-- title:
--   Dusart Table 1 intervals for the fourth-logarithmic theta estimate
-- statement:
--   Each record contains the lower exponent $b$, the next exponent $c$, and the exact rational upper bound $\varepsilon_b$ printed in Dusart's Table 1. The 39 intervals cover $23\le\log x\le10000$. The analytic exponential estimate handles larger arguments.
--
--   The records are data only: the uniform inequalities $|\psi(x)-x|\le\varepsilon_b x$ are separate theorem obligations.
-- source:
--   P. Dusart, Explicit estimates of some functions over primes, Ramanujan J.45 (2018), Table 1, printed pp.234–235. https://piyanit.nl/wp-content/uploads/2020/10/art_10.1007_s11139-016-9839-4.pdf. The rows b=23 through b=9000 are transcribed; next endpoints form a derived coverage partition ending at 10000.

import Mathlib.Data.Rat.Defs
import Mathlib.Data.List.Basic

namespace DusartThetaTable

/-- An interval and its rounded-up Table 1 relative psi-error bound. -/
structure Row where
  b : ℕ
  next : ℕ
  epsilon : ℚ
  deriving DecidableEq

/-- Dusart (2018), Table 1, printed pp. 234–235.
The rows below 23 are replaced by the finite certificate; the exponential
estimate replaces the rows at and above 10000. -/
def rows : List Row :=
  [⟨23, 24, 2431 / 10^7⟩,
   ⟨24, 25, 1496 / 10^7⟩,
   ⟨25, 30, 9250 / 10^8⟩,
   ⟨30, 35, 9647 / 10^9⟩,
   ⟨35, 40, 1078 / 10^9⟩,
   ⟨40, 45, 1161 / 10^10⟩,
   ⟨45, 50, 1225 / 10^11⟩,
   ⟨50, 55, 1275 / 10^12⟩,
   ⟨55, 60, 1388 / 10^13⟩,
   ⟨60, 65, 2978 / 10^14⟩,
   ⟨65, 70, 2039 / 10^14⟩,
   ⟨70, 75, 1940 / 10^14⟩,
   ⟨75, 80, 1913 / 10^14⟩,
   ⟨80, 85, 1893 / 10^14⟩,
   ⟨85, 90, 1868 / 10^14⟩,
   ⟨90, 95, 1847 / 10^14⟩,
   ⟨95, 100, 1830 / 10^14⟩,
   ⟨100, 200, 1815 / 10^14⟩,
   ⟨200, 300, 1557 / 10^14⟩,
   ⟨300, 400, 1404 / 10^14⟩,
   ⟨400, 500, 1288 / 10^14⟩,
   ⟨500, 600, 1215 / 10^14⟩,
   ⟨600, 700, 1115 / 10^14⟩,
   ⟨700, 800, 1039 / 10^14⟩,
   ⟨800, 900, 9826 / 10^15⟩,
   ⟨900, 1000, 9281 / 10^15⟩,
   ⟨1000, 1500, 8743 / 10^15⟩,
   ⟨1500, 2000, 5311 / 10^15⟩,
   ⟨2000, 2500, 2536 / 10^15⟩,
   ⟨2500, 3000, 8941 / 10^16⟩,
   ⟨3000, 3500, 3156 / 10^16⟩,
   ⟨3500, 4000, 1116 / 10^16⟩,
   ⟨4000, 4500, 3946 / 10^17⟩,
   ⟨4500, 5000, 1274 / 10^17⟩,
   ⟨5000, 6000, 3956 / 10^18⟩,
   ⟨6000, 7000, 4893 / 10^19⟩,
   ⟨7000, 8000, 6393 / 10^20⟩,
   ⟨8000, 9000, 8969 / 10^21⟩,
   ⟨9000, 10000, 2427 / 10^21⟩]

end DusartThetaTable


