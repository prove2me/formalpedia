-- Prove2me | Definitions.Def_BosonicLearn_fugacityFamily
-- name    : BosonicLearn_fugacityFamily
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T07:26:29.383205+00:00
-- url     : https://prove2.me/theorems/08a2450c-50e3-421a-bf3e-f6aec30df2fa
-- title:
--   The fugacity family $R_X=r(I+\xi X)$, $r=\nu/((1-4\xi)(1+\nu))$
-- statement:
--   For $\nu>0$, a small parameter $\xi\in(0,1/32)$ and $X\in\mathrm{Herm}_0(n)$,
--
--   $$R_X=r(I+\xi X),\qquad r=\frac{\nu}{(1-4\xi)(1+\nu)} .$$
--
--   For $X\in G_{\mathrm{supp}}$ and $\nu\le1$ one has $\frac{\nu}{1+\nu}I\preceq R_X\preceq\frac{2\nu}{1+2\nu}I$, so the states $\rho_{R_X}$ satisfy $(\tfrac12+\nu)I\preceq\Sigma\preceq(\tfrac12+2\nu)I$.
-- source:
--   Chen, Anna Mele, Anna Mele, Preskill, When are bosonic Gaussian states classical to learn?, arXiv:2609.26705, §5.1, Eqs. (30)–(31), p. 30

import Mathlib
import Definitions.Def_BosonicLearn_Herm0

namespace BosonicLearn

/-- **The fugacity family `R_X = r(I + ξX)`.**
Chen, Anna Mele, Anna Mele, Preskill, *When are bosonic Gaussian states classical to learn?*, arXiv:2609.26705, §5.1, Eqs. (30)–(31), p. 30: "Define the following family of fugacity matrices: R_X := r(I + ξX) for
X ∈ Herm_0(n) … The parameter r is chosen as r := ν/((1 − 4ξ)(1 + ν))."

`fugacityFamily ν ξ X = (ν / ((1 − 4ξ)(1 + ν))) · (I + ξ X)`. -/
noncomputable def fugacityFamily {n : ℕ} (ν ξ : ℝ) (X : Herm0 n) : Matrix (Fin n) (Fin n) ℂ :=
  ((ν / ((1 - 4 * ξ) * (1 + ν)) : ℝ) : ℂ) • (1 + (ξ : ℂ) • (X : Matrix (Fin n) (Fin n) ℂ))

end BosonicLearn


