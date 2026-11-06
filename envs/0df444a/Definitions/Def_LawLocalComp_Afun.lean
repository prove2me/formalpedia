-- Prove2me | Definitions.Def_LawLocalComp_Afun
-- name    : LawLocalComp_Afun
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T03:10:17.027511+00:00
-- url     : https://prove2.me/theorems/748c31a8-b568-40d5-b14b-d54332213002
-- title:
--   Structured atom order $A(\varepsilon,M)$
-- statement:
--   $$A(\varepsilon,M)=\varepsilon^{-1}\log\Big(1+\sqrt{\varepsilon\log(M+1)}\Big),$$
--   the sharp resource–accuracy crossover for lattice-log-concave and conditional-IFR laws.
--
--   **Formalization Note** $\log$ is the natural logarithm; another base rescales $\sqrt{\varepsilon\log(M+1)}$ by a constant, which changes $A$ by a bounded factor.
-- source:
--   Mahboub–Rahgoshay, Optimal Law-Local Compression for Stochastic Loads, STOC 2027 submission (manuscript of Oct. 29, 2026, sha256 5f71501c…aa873), (3), p.2

import Mathlib

namespace LawLocalComp

/-- **The structured atom order `A(ε, M)`.**
Mahboub–Rahgoshay, *Optimal Law-Local Compression for Stochastic Loads*, STOC 2027
submission manuscript of Oct. 29, 2026 (sha256 5f71501c…aa873), (3), p.2: `A(ε, M) = ε⁻¹ log(1 + √(ε log(M + 1)))`.

**Formalization Note.** `log` is the natural logarithm; another base changes `√(ε log(M+1))` by a
constant factor inside `log(1 + ·)`, hence `A` by a bounded factor. -/
noncomputable def Afun (ε : ℝ) (M : ℕ) : ℝ :=
  ε⁻¹ * Real.log (1 + Real.sqrt (ε * Real.log (M + 1)))

end LawLocalComp


