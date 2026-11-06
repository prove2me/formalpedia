-- Prove2me | Definitions.Def_GradSuffice_thm8Kappa
-- name    : GradSuffice_thm8Kappa
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:20:32.481533+00:00
-- url     : https://prove2.me/theorems/d2948533-abbf-4157-bc80-f10783f5990d
-- title:
--   The number of copies $\kappa=\lfloor\log(1/(4\varepsilon))/\log(1/s)\rfloor$
-- statement:
--   For $0<\varepsilon\le s/4$ the hard instance of Theorem 8 stacks
--   $$\kappa:=\Big\lfloor\frac{\log(1/(4\varepsilon))}{\log(1/s)}\Big\rfloor$$
--   copies, so that $s^\kappa\ge4\varepsilon$. Here $\log$ is the natural logarithm; for $\varepsilon\le s/4$ one has $\kappa\ge1$.
-- source:
--   Alon–Koren–Livni–Moran, When Do Gradients Suffice? A Characterization of First-Order Convex Optimization, manuscript of November 3, 2026 (STOC 2027 submission), Theorem 8, p.18

import Mathlib
import Definitions.Def_GradSuffice_thm8S

namespace GradSuffice

/-- **The number of copies `κ := ⌊log(1/(4ε)) / log(1/s)⌋`.** Alon–Koren–Livni–Moran, *When Do Gradients Suffice?*, manuscript of November 3, 2026, Theorem 8, p.18 ("For every
`0 < ε ≤ s/4`, define `κ := ⌊log(1/(4ε))/log(1/s)⌋`").

**Formalization Note.** `log` is the natural logarithm (no base is printed). For `0 < ε ≤ s/4` the
quotient is at least `1`, so `κ ≥ 1`. -/
noncomputable def thm8Kappa (θ ε : ℝ) : ℕ :=
  ⌊Real.log (1 / (4 * ε)) / Real.log (1 / thm8S θ)⌋₊

end GradSuffice


