-- Prove2me | Definitions.Def_AgnGaussTomo_LL
-- name    : AgnGaussTomo_LL
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T20:20:20.092204+00:00
-- url     : https://prove2.me/theorems/8ecbfbd8-dd0e-4ecf-b5b6-2693873db735
-- title:
--   Corrected double logarithm $L(\kappa)=\max(1,\log\log\kappa)$
-- statement:
--   For $\kappa\in\mathbb R$ let
--
--   $$
--   L(\kappa)=\max\{1,\ \log\log\kappa\}.
--   $$
--
--   The paper's copy counts for Theorems 3.4, 3.6 and 3.8 carry the factor $\log\log\|V^{-1}\|_{\mathrm{op}}$. That factor is non-positive when $\|V^{-1}\|_{\mathrm{op}}\le e$ and equals $-\infty$ at $\|V^{-1}\|_{\mathrm{op}}=1$ (the vacuum and all coherent states), so read literally it would allow zero copies, which is impossible. $L$ is the standard repair; it coincides with $\log\log\kappa$ once $\kappa\ge e^{e}$.
--
--   **Formalization Note** $\log$ is the natural logarithm (`Real.log`, which returns $0$ on non-positive arguments; this never matters because of the maximum with $1$).
-- source:
--   Arulandu, Chen, Chen, Li, Ma, Finding Gaussian Structure in Bosonic States, arXiv:2610.06810 (version of 3 Nov 2026), Theorems 3.4, 3.6, 3.8, printed pp. 16–18 (PDF pp. 19–21); correction of the factor log log ‖V^{-1}‖_op

import Mathlib

namespace AgnGaussTomo

/-- **The corrected double-logarithmic factor `L(κ) = max(1, log log κ)`.** Arulandu, Chen, Chen, Li,
Ma, *Finding Gaussian Structure in Bosonic States*, arXiv:2610.06810 (version of 3 Nov 2026),
Theorems 3.4, 3.6, 3.8, printed pp. 16–18 (PDF pp. 19–21), whose copy counts carry the factor
`log log ‖V^{-1}‖_op`.

**Formalization Note (correction).** The printed factor `log log ‖V^{-1}‖_op` is `≤ 0` when
`‖V^{-1}‖_op ≤ e` (and undefined, `−∞`, at `‖V^{-1}‖_op = 1`, e.g. the vacuum or coherent
states), so read literally it allows zero copies in Theorems 3.4, 3.6 and 3.8 for small `δ`, which
is false (two coherent states `|±α⟩`, `|α| = 1`, cannot both be learned from zero copies). The
standard convention `max(1, log log ·)` is used; it equals the printed factor once the argument is
at least `e^e`. `Real.log` is the natural logarithm (`Real.log x = 0` for `x ≤ 0`, irrelevant
because of the `max`). -/
noncomputable def LL (κ : ℝ) : ℝ := max 1 (Real.log (Real.log κ))

end AgnGaussTomo


