-- Prove2me | Definitions.Def_RamanujanLostNotebook_PartIII_ch07_tau2
-- name    : RamanujanLostNotebook_PartIII_ch07_tau2
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-10-08T21:25:32.308326+00:00
-- url     : https://prove2.me/theorems/fc8ac108-1cd9-4975-b0c9-15e67d32cbf7
-- title:
--   Ramanujan's Lost Notebook Part III, Ch. 7: tau2
-- statement:
--   Generalized tau function `τ_2(n)`, defined by `∑_{n ≥ 1} τ_2(n) q^n = Q(q) Δ(τ)`
--   ((7.1.1), p. 205): the coefficient of `q^n` in `Q Δ`, read off the product of the truncations
--   `eisensteinQTrunc n` and `deltaTrunc n`, which is exact in degree `n`.  `τ_2(0) = 0`.
--   Reference: `τ_2(1), …, τ_2(6) = 1, 216, -3348, 13888, 52110, -723168`.
-- source:
--   G. E. Andrews and B. C. Berndt, Ramanujan's Lost Notebook, Part III, Springer 2012, Chapter 7.

import Mathlib
import Definitions.Def_RamanujanLostNotebook_PartIII_ch07_deltaTrunc
import Definitions.Def_RamanujanLostNotebook_PartIII_ch07_eisensteinQTrunc

namespace RamanujanLostNotebook.PartIII

/-- Generalized tau function `τ_2(n)`, defined by `∑_{n ≥ 1} τ_2(n) q^n = Q(q) Δ(τ)`
((7.1.1), p. 205): the coefficient of `q^n` in `Q Δ`, read off the product of the truncations
`eisensteinQTrunc n` and `deltaTrunc n`, which is exact in degree `n`.  `τ_2(0) = 0`.
Reference: `τ_2(1), …, τ_2(6) = 1, 216, -3348, 13888, 52110, -723168`. -/
noncomputable def tau2 (n : ℕ) : ℤ :=
  (eisensteinQTrunc n * deltaTrunc n).coeff n

end RamanujanLostNotebook.PartIII


