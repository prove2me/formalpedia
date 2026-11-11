-- Prove2me | Definitions.Def_SumReLU_Stensor
-- name    : SumReLU_Stensor
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T08:27:40.573315+00:00
-- url     : https://prove2.me/theorems/20bded5d-7195-4ee3-9572-a29cafc1e1cc
-- title:
--   The moment STC output $S_t(x,y,z)=\frac{y}{\hat\sigma_t\sqrt{t!}}\mathrm{Re}((x+iz)^{\otimes t})$
-- statement:
--   For $x,z\in\mathbb R^d$, a label $y$ and $t\in\mathbb Z_+$,
--   $$
--   S_t(x,y,z)=\frac{y}{\hat\sigma_t\sqrt{t!}}\,\mathrm{Re}\big((x+iz)^{\otimes t}\big),\qquad (S_t)_{i_1\dots i_t}=\frac{y}{\hat\sigma_t\sqrt{t!}}\,\mathrm{Re}\prod_{m=1}^t(x_{i_m}+iz_{i_m}).
--   $$
--   With $z\sim N(0,I_d)$ independent of an example $(x,y)$, its mean is $\sum_i\beta_iw_i^{\otimes t}$ for even $t$ (Lemma 4.17); the paper estimates the compressor from samples of $S_t$.
-- source:
--   Diakonikolas, Diakonikolas, Wang, Zarifis, Learning Positive Linear Combinations of ReLUs in Fully Polynomial Time, arXiv:2610.32940 (PDF sha256 66803576…6c48), Lemma 4.17, Equation (20), p.36 (PDF p.38)

import Mathlib
import Definitions.Def_SumReLU_reluHermite

namespace SumReLU

/-- The STC output `S_t(x, y, z) = (y/(σ̂_t √(t!))) Re((x + iz)^{⊗t})`, entrywise:
`(S_t)_J = (y/(σ̂_t √(t!))) · Re ∏_{m<t} (x_{J_m} + i z_{J_m})`.

Diakonikolas, Diakonikolas, Wang, Zarifis, *Learning Positive Linear Combinations of ReLUs in
Fully Polynomial Time*, arXiv:2610.32940 (PDF sha256 66803576…6c48), Lemma 4.17, Equation (20), p.36 (PDF p.38). -/
noncomputable def Stensor {d : ℕ} (t : ℕ) (x : EuclideanSpace ℝ (Fin d)) (y : ℝ)
    (z : EuclideanSpace ℝ (Fin d)) (J : Fin t → Fin d) : ℝ :=
  (y / (reluHermite t * Real.sqrt (t.factorial : ℝ))) *
    (∏ m, ((x (J m) : ℂ) + Complex.I * (z (J m) : ℂ))).re

end SumReLU


