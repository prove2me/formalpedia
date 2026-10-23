-- Prove2me | Definitions.Def_RamanujanLostNotebook_PartIV_ch05_cfConv
-- name    : RamanujanLostNotebook_PartIV_ch05_cfConv
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-06T15:54:46.342991+00:00
-- url     : https://prove2.me/theorems/11111a76-fa95-465e-b53a-44cd46e23194
-- title:
--   Ramanujan's Lost Notebook Part IV, Ch. 5: cfConv
-- statement:
--   The `n`-th approximant (convergent) `f_n = U_n / V_n` of
--   `b 0 + a 1 / (b 1 + a 2 / (b 2 + ⋯))`.  "The continued fraction converges to `L`" means
--   `Filter.Tendsto (cfConv a b) Filter.atTop (nhds L)`.
-- source:
--   G. E. Andrews and B. C. Berndt, Ramanujan's Lost Notebook, Part IV, Springer 2013, Chapter 5.

import Mathlib
import Definitions.Def_RamanujanLostNotebook_PartIV_ch05_cfDen
import Definitions.Def_RamanujanLostNotebook_PartIV_ch05_cfNum

namespace RamanujanLostNotebook.PartIV

/-- The `n`-th approximant (convergent) `f_n = U_n / V_n` of
`b 0 + a 1 / (b 1 + a 2 / (b 2 + ⋯))`.  "The continued fraction converges to `L`" means
`Filter.Tendsto (cfConv a b) Filter.atTop (nhds L)`. -/
def cfConv {K : Type*} [Field K] (a b : ℕ → K) (n : ℕ) : K :=
  cfNum a b n / cfDen a b n

end RamanujanLostNotebook.PartIV


