-- Prove2me | Definitions.Def_SmoothedNash_Supplement_lipJK
-- name    : SmoothedNash_Supplement_lipJK
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T23:02:59.4942+00:00
-- url     : https://prove2.me/theorems/c7050baf-09a1-4616-84e9-9e8138ecec40
-- title:
--   Lipschitz bound $L_J = 2L_2/a + 2(1 + L_1/a)$
-- statement:
--   With $a = L_0 + L_1$, the Lipschitz bound of the homotopy Jacobian on $B(0,1) \times [-1, 2]$ is
--   $$
--   L_J = \frac{2L_2}{a} + 2\Bigl(1 + \frac{L_1}{a}\Bigr).
--   $$
--   It sets the step size of Algorithm 4 and appears in the bounds of Theorem 4.5.
-- source:
--   Attias–Dagan–Daskalakis–Yao–Zampetakis, Nash Equilibria, Variational Inequalities, and Fixed Points: Beating Brute Force via Smoothed Analysis, STOC 2027 submission (manuscript sha256 3f9ea37d…77a1ea53), §4.1.2, p.26, and Algorithm 4, line 5, p.28

import Mathlib
open MeasureTheory

namespace SmoothedNash.Supplement

/-- The Lipschitz bound `L_J = 2 L2/a + 2 (1 + L1/a)` of the homotopy Jacobian, with
`a = L0 + L1` (Attias–Dagan–Daskalakis–Yao–Zampetakis, *Nash Equilibria, Variational Inequalities, and Fixed Points: Beating Brute Force via Smoothed Analysis*, STOC 2027 submission manuscript (sha256 3f9ea37d…77a1ea53), §4.1.2, p.26, and Algorithm 4, line 5, p.28). -/
noncomputable def lipJK (L0 L1 L2 : ℝ) : ℝ :=
  2 * L2 / (L0 + L1) + 2 * (1 + L1 / (L0 + L1))

end SmoothedNash.Supplement


