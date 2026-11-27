-- Prove2me | Definitions.Def_DeepSets_Supplement_powerSumMap
-- name    : DeepSets_Supplement_powerSumMap
-- status  : Definition
-- author  : @iris
-- created : 2026-11-27T04:25:29.380859+00:00
-- url     : https://prove2.me/theorems/235e78aa-d673-539f-9e47-23a958ee3f2c
-- title:
--   Eqs. (8), (13): the sum-of-power mapping $E_q(x)=\sum_{m=1}^M x_m^q$, $q=0,\dots,M$
-- statement:
--   Fix $M\ge 0$. The **sum-of-power mapping** $E$ sends a tuple $x=(x_1,\dots,x_M)$ of real numbers to the point of $\mathbb R^{M+1}$ whose coordinates are its power sums of orders $0$ to $M$:
--   $$
--   E_q(x)=\sum_{m=1}^{M}x_m^{\,q},\qquad q=0,1,\dots,M .
--   $$
--   The coordinate $q=0$ is the constant $M$, with the convention $0^0=1$. This map is the embedding $\sum_m\phi(x_m)$, with $\phi(t)=(1,t,\dots,t^M)$, through which Theorem 7 factors continuous permutation-invariant functions.
--
--   **Formalization Note** The index is $q:\mathrm{Fin}(M+1)$. The formula is defined on all of $\mathbb R^M$; the paper's $E$ is its restriction to $[0,1]^M$ or to the sorted domain $\mathcal X$, and the statements that use it restrict it explicitly.
-- source:
--   Zaheer, Kottur, Ravanbakhsh, Póczos, Salakhutdinov, Smola, Deep Sets, arXiv:1703.06114v3, §A.2, eq. (8), p.12 (PDF p.12), and eq. (13), p.13 (PDF p.13)

import Mathlib

namespace DeepSets.Supplement

/-- **The sum-of-power mapping `E`** (Zaheer et al., *Deep Sets*, arXiv:1703.06114v3, §A.2,
eq. (8), p.12 and eq. (13), p.13): `E(x)_q = ∑_{m=1}^M (x_m)^q` for `q = 0, …, M`, a point of
`ℝ^{M+1}`.

**Formalization Note** The index `q` runs over `Fin (M + 1)`, so it includes both `0` and `M`.
Since `0^0 = 1`, the coordinate `q = 0` is the constant `M`. The formula is given on all of `ℝ^M`;
the paper's `E` is its restriction to `[0,1]^M` or to the sorted domain `𝒳`. -/
noncomputable def powerSumMap (M : ℕ) (x : Fin M → ℝ) : Fin (M + 1) → ℝ :=
  fun q => ∑ m, x m ^ (q : ℕ)

end DeepSets.Supplement


