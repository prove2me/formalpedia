-- Prove2me | Definitions.Def_ShallowShadows_ShadowNorm_prob
-- name    : ShallowShadows_ShadowNorm_prob
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:31:11.955512+00:00
-- url     : https://prove2.me/theorems/47b1cb07-5b6f-4222-89ac-1d54be6c86d0
-- title:
--   $\Pr_{U\sim\mathcal U}(A(U))$ for a finite ensemble
-- statement:
--   For a finite ensemble $\mathcal U$ of unitaries $U_i$ drawn with probabilities $w_i$ and a property $A$ of unitaries,
--
--   $$
--   \Pr_{U\sim\mathcal U}(A(U)) = \sum_i w_i\,[A(U_i)].
--   $$
--
--   This is the probability in the definitions of $t_{\lambda,d}$ and $\tau_{(\lambda,\lambda'),d}$.
-- source:
--   Bertoni, Haferkamp, Hinsche, Ioannou, Eisert, Pashayan, Shallow shadows: Expectation estimation using low-depth random Clifford circuits, arXiv:2209.12924v3, Eqs. (5) and (19), pp. 4 and 7

import Mathlib
import Definitions.Def_ClassicalShadow_Linear_Setting

open ClassicalShadow.Linear

namespace ShallowShadows.ShadowNorm

open Classical in
/-- Bertoni, Haferkamp, Hinsche, Ioannou, Eisert, Pashayan, *Shallow shadows: Expectation
estimation using low-depth random Clifford circuits*, arXiv:2209.12924v3, Eqs. (5) and (19),
pp. 4 and 7: `Pr_{U∼𝒰}(A(U))`, the probability that a unitary drawn from the finite ensemble `𝒰`
satisfies `A`, i.e. `Σ_i w_i [A(U_i)]`. -/
noncomputable def prob {n : ℕ} {ι : Type} [Fintype ι] (E : Primitive n ι)
    (A : Matrix.unitaryGroup (Bits n) ℂ → Prop) : ℝ :=
  ∑ i, if A (E.U i) then E.w.prob i else 0

end ShallowShadows.ShadowNorm


