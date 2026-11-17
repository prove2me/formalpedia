-- Prove2me | Definitions.Def_LawLocalComp_Supplement_envOrder
-- name    : LawLocalComp_Supplement_envOrder
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T14:07:31.405399+00:00
-- url     : https://prove2.me/theorems/c3311183-ab8f-45f4-9082-90d914f4aa31
-- title:
--   The envelope atom order $\min\{\sqrt{U L_U/\varepsilon}, L_U/\varepsilon\}$ (45)
-- statement:
--   For $\varepsilon > 0$ and a resource scale $M$, put $U = \ln(M + 1)$ and $L_U = \ln(2 + U)$. The **envelope order** is
--   $$
--   \min\Bigl\{\sqrt{\tfrac{U\,L_U}{\varepsilon}},\ \tfrac{L_U}{\varepsilon}\Bigr\}. \tag{45}
--   $$
--   Theorem 9.3 shows that it is the sharp atom count for the sub-Weibull class of Definition 9.1.
--
--   **Formalization Note** Natural logarithms, as printed.
-- source:
--   Mahboub–Rahgoshay, Optimal Law-Local Compression for Stochastic Loads, STOC 2027 submission (manuscript of Oct. 29, 2026, sha256 5f71501c…aa873), Theorem 9.3, (45), p.16

import Mathlib

namespace LawLocalComp

namespace Supplement

/-- **The envelope atom order (45).**
Mahboub–Rahgoshay, *Optimal Law-Local Compression for Stochastic Loads*, STOC 2027
submission manuscript of Oct. 29, 2026 (sha256 5f71501c…aa873), Theorem 9.3, (45), p.16: with `U = ln(M + 1)` and `LU = ln(2 + U)`, the order is
`min{√(U · LU/ε), LU/ε}`.

**Formalization Note.** Natural logarithms, as printed. -/
noncomputable def envOrder (ε : ℝ) (M : ℕ) : ℝ :=
  min (Real.sqrt (Real.log ((M : ℝ) + 1) * Real.log (2 + Real.log ((M : ℝ) + 1)) / ε))
    (Real.log (2 + Real.log ((M : ℝ) + 1)) / ε)

end Supplement

end LawLocalComp


