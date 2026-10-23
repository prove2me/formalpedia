-- Prove2me | Definitions.Def_RamanujanLostNotebook_PartV_shared_univG3
-- name    : RamanujanLostNotebook_PartV_shared_univG3
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-06T16:06:46.883978+00:00
-- url     : https://prove2.me/theorems/8c6f2f63-8146-40c2-81a8-734ae888283b
-- title:
--   Ramanujan's Lost Notebook Part V, shared: univG3
-- statement:
--   Universal mock theta function of odd order
--   `g_3(x, q) = ∑_{n ≥ 0} q^{n(n+1)} / ((x; q)_{n+1} (q/x; q)_{n+1})` ((12.5.2), p. 288).
--   It is the same series as `g_3(z; q) = ∑_{m ≥ 1} q^{m(m-1)} / ((z; q)_m (q/z; q)_m)` of
--   (13.1.7), p. 294, and as the first sum in (6.4.11), p. 92.
--
--   Domain: `‖q‖ < 1`, `x ≠ 0`, `x ≠ q^k` for every integer `k`.  There
--   `g_3(x, q) = (q; q)_∞^{-1} ∑_{n ∈ ℤ} (-1)^n q^{3n(n+1)/2} / (1 - x q^n)` ((6.4.11)).
--   Outside: `x = 0` or a pole gives junk (terms with zero denominator are `0`).
--   Reference: `g_3(-1, 1/5) = 0.43004175144600103428…`.
-- source:
--   G. E. Andrews and B. C. Berndt, Ramanujan's Lost Notebook, Part V, Springer 2018.

import Mathlib
import Definitions.Def_RamanujanLostNotebook_PartV_shared_qPoch

noncomputable section

namespace RamanujanLostNotebook.PartV

/-- Universal mock theta function of odd order
`g_3(x, q) = ∑_{n ≥ 0} q^{n(n+1)} / ((x; q)_{n+1} (q/x; q)_{n+1})` ((12.5.2), p. 288).
It is the same series as `g_3(z; q) = ∑_{m ≥ 1} q^{m(m-1)} / ((z; q)_m (q/z; q)_m)` of
(13.1.7), p. 294, and as the first sum in (6.4.11), p. 92.

Domain: `‖q‖ < 1`, `x ≠ 0`, `x ≠ q^k` for every integer `k`.  There
`g_3(x, q) = (q; q)_∞^{-1} ∑_{n ∈ ℤ} (-1)^n q^{3n(n+1)/2} / (1 - x q^n)` ((6.4.11)).
Outside: `x = 0` or a pole gives junk (terms with zero denominator are `0`).
Reference: `g_3(-1, 1/5) = 0.43004175144600103428…`. -/
def univG3 (x q : ℂ) : ℂ :=
  ∑' n : ℕ, q ^ (n * (n + 1)) / (qPoch x q (n + 1) * qPoch (q / x) q (n + 1))

end RamanujanLostNotebook.PartV

end


