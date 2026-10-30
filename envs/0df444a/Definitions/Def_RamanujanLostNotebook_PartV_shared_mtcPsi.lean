-- Prove2me | Definitions.Def_RamanujanLostNotebook_PartV_shared_mtcPsi
-- name    : RamanujanLostNotebook_PartV_shared_mtcPsi
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-10-06T16:06:02.604369+00:00
-- url     : https://prove2.me/theorems/154f3c30-d373-4ccf-92ed-3cfb86c9655d
-- title:
--   Ramanujan's Lost Notebook Part V, shared: mtcPsi
-- statement:
--   `Ψ(q) = -1 + ∑_{n ≥ 0} q^{5n^2} / ((q^2; q^5)_{n+1} (q^3; q^5)_n)` ((5.1.13), p. 60;
--   `q` times the series of (19.2.8), p. 391).  Domain: `‖q‖ < 1`.
--   Reference: `q^2 + q^4 + q^5 + q^6 + q^7 + 2q^8 + q^9 + 2q^10 + …`,
--   `Ψ(1/5) = 0.042002692473184344959…`.
-- source:
--   G. E. Andrews and B. C. Berndt, Ramanujan's Lost Notebook, Part V, Springer 2018.

import Mathlib
import Definitions.Def_RamanujanLostNotebook_PartV_shared_qPoch

noncomputable section

namespace RamanujanLostNotebook.PartV

/-- `Ψ(q) = -1 + ∑_{n ≥ 0} q^{5n^2} / ((q^2; q^5)_{n+1} (q^3; q^5)_n)` ((5.1.13), p. 60;
`q` times the series of (19.2.8), p. 391).  Domain: `‖q‖ < 1`.
Reference: `q^2 + q^4 + q^5 + q^6 + q^7 + 2q^8 + q^9 + 2q^10 + …`,
`Ψ(1/5) = 0.042002692473184344959…`. -/
def mtcPsi (q : ℂ) : ℂ :=
  -1 + ∑' n : ℕ, q ^ (5 * n ^ 2) / (qPoch (q ^ 2) (q ^ 5) (n + 1) * qPoch (q ^ 3) (q ^ 5) n)

end RamanujanLostNotebook.PartV

end


