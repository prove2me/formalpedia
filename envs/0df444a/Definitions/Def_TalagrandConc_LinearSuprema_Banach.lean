-- Prove2me | Definitions.Def_TalagrandConc_LinearSuprema_Banach
-- name    : TalagrandConc_LinearSuprema_Banach
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T17:44:44.537005+00:00
-- url     : https://prove2.me/theorems/f884abc3-0d59-4195-ab1b-51014a17f2d6
-- title:
--   Weak variance parameter for a finite family of Banach-space vectors
-- statement:
--   For vectors $v_1,\ldots,v_N$ in a real normed space $W$, define the weak variance scale
--   $$\sigma=\left(\sup_{w^*\in W^*,\,\|w^*\|\le1}\sum_{i=1}^N w^*(v_i)^2\right)^{1/2}.$$
--   For real coefficients $y_i$, also define $S(y)=\|\sum_i y_i v_i\|$.
--
--   These are the scale and random norm appearing in Theorem 13.2.
--
--   **Formalization Note** $W^*$ is the continuous real dual. The supremum is over its closed unit ball.
-- source:
--   Talagrand, Concentration of measure and isoperimetric inequalities in product spaces, Publ. Math. IHÉS 81 (1995), p. 198, Eq. (13.10) and Theorem 13.2

import Mathlib

namespace TalagrandConc.LinearSuprema

noncomputable def weakSigma {N : ℕ} {W : Type*} [NormedAddCommGroup W]
    [NormedSpace ℝ W] (v : Fin N → W) : ℝ :=
  Real.sqrt (sSup ((fun φ : W →L[ℝ] ℝ => ∑ i, (φ (v i)) ^ 2) ''
    {φ : W →L[ℝ] ℝ | ‖φ‖ ≤ 1}))

def vectorSumNorm {N : ℕ} {W : Type*} [NormedAddCommGroup W]
    [NormedSpace ℝ W] (v : Fin N → W) (y : Fin N → ℝ) : ℝ :=
  ‖∑ i, (y i) • (v i)‖

end TalagrandConc.LinearSuprema


