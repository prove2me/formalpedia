-- Prove2me | Definitions.Def_TIESharp_rho
-- name    : TIESharp_rho
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:38:54.075664+00:00
-- url     : https://prove2.me/theorems/d318b5bd-a107-4a96-a814-0dd206143805
-- title:
--   Optimal truthful-in-expectation ratio $\rho(n)$
-- statement:
--   For fixed $n$, $\rho(n)$ is the infimum of the finite bounds $R$ for which some feasible, truthful-in-expectation family is $R$-approximate:
--   $$\rho(n)=\inf\{R\in\mathbb R:\ \exists\text{ a feasible truthful-in-expectation family that is }R\text{-approximate}\}.$$
--
--   **Formalization Note.** The infimum is `sInf` on `ℝ`, which returns $0$ on the empty set; statements about `rho` in this mission also assert attainment and a lower bound, so no junk value is used.
-- source:
--   Li, Sharp Bounds for Truthful-in-Expectation Scheduling, arXiv:2611.05134 (held version, sha256 e611c390…b70e5481), §2, p.4

import Mathlib
import Definitions.Def_TIESharp_IsFeasible
import Definitions.Def_TIESharp_IsTIE
import Definitions.Def_TIESharp_IsRApprox

set_option autoImplicit false

namespace TIESharp

/-- The **optimal truthful-in-expectation approximation ratio** `ρ(n)` (Li, *Sharp Bounds for
Truthful-in-Expectation Scheduling*, arXiv:2611.05134, §2, p.4): "The infimum of such finite
bounds over truthful-in-expectation families at fixed n is ρ(n)", i.e. the infimum of all real `R`
for which some feasible, truthful-in-expectation family is `R`-approximate.

**Formalization Note.** The infimum is `sInf` on `ℝ`. It returns `0` on an empty set and a junk
value on a set unbounded below; every statement about `rho` in this mission also asserts that the
set is nonempty (attainment) and bounded below (the lower bound), so no junk value is used. -/
noncomputable def rho (n : ℕ) : ℝ :=
  sInf {R : ℝ | ∃ F : Family n, IsFeasible F ∧ IsTIE F ∧ IsRApprox F R}

end TIESharp


