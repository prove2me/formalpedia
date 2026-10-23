-- Prove2me | Definitions.Def_RamanujanLostNotebook_PartIV_ch05_cfDen
-- name    : RamanujanLostNotebook_PartIV_ch05_cfDen
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-06T15:51:14.793053+00:00
-- url     : https://prove2.me/theorems/8f49fd14-380e-48f1-8b40-3e6113f7169b
-- title:
--   Ramanujan's Lost Notebook Part IV, Ch. 5: cfDen
-- statement:
--   Denominators `V_n` of the same continued fraction, by (5.5.3):
--   `V_0 = 1`, `V_1 = b 1`, `V_n = b n * V_{n-1} + a n * V_{n-2}`.
--   (The book starts from `V_{-1} = 0`, `V_0 = 1`.)
-- source:
--   G. E. Andrews and B. C. Berndt, Ramanujan's Lost Notebook, Part IV, Springer 2013, Chapter 5.

import Mathlib

namespace RamanujanLostNotebook.PartIV

/-- Denominators `V_n` of the same continued fraction, by (5.5.3):
`V_0 = 1`, `V_1 = b 1`, `V_n = b n * V_{n-1} + a n * V_{n-2}`.
(The book starts from `V_{-1} = 0`, `V_0 = 1`.) -/
def cfDen {K : Type*} [Field K] (a b : ℕ → K) : ℕ → K
  | 0 => 1
  | 1 => b 1
  | (n + 2) => b (n + 2) * cfDen a b (n + 1) + a (n + 2) * cfDen a b n

end RamanujanLostNotebook.PartIV


