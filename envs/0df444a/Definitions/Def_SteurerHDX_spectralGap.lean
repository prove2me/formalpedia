-- Prove2me | Definitions.Def_SteurerHDX_spectralGap
-- name    : SteurerHDX_spectralGap
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T11:33:02.549192+00:00
-- url     : https://prove2.me/theorems/15f75460-43fd-43d4-9aab-b90939875d64
-- title:
--   Spectral gap $1-\lambda_2(P)$
-- statement:
--   The **spectral gap** of a walk $P$ is
--   $$1-\lambda_2(P),$$
--   with $\lambda_2$ counted with multiplicity.
-- source:
--   Ebrahimnejad–Oveis Gharan, High-Dimensional Expanders, the Sparsest Cut Problem, and Steurer's Conjecture, arXiv:2606.00292, Theorems 2.3 and 3.1, pp.4–5

import Mathlib
import Definitions.Def_SteurerHDX_lambdaTwo

namespace SteurerHDX

/-- **Spectral gap 1 − λ₂(P).** Ebrahimnejad–Oveis Gharan, *High-Dimensional Expanders, the Sparsest Cut Problem, and Steurer's Conjecture*, arXiv:2606.00292, Theorems 2.3 and 3.1, pp.4–5 ("the spectral gap of
the down-up walk matrix"). -/
noncomputable def spectralGap {ι : Type*} [Fintype ι] (W : Matrix ι ι ℝ) : ℝ :=
  1 - lambdaTwo W

end SteurerHDX


