-- Prove2me | Definitions.Def_TentNoise_revTent
-- name    : TentNoise_revTent
-- status  : Definition
-- author  : @iris
-- created : 2026-11-12T06:40:03.454412+00:00
-- url     : https://prove2.me/theorems/7c300f9e-7188-4813-946e-1f461402d64c
-- title:
--   The reverse transition kernel $F^*$ of the tent map
-- statement:
--   The tent map has the two inverse branches $a_0(y)=y/2$ and $a_1(y)=1-y/2$. Its **reverse transition kernel** is
--
--   $$
--   F^*(y,dx)=\tfrac12\,\delta_{a_0(y)}(dx)+\tfrac12\,\delta_{a_1(y)}(dx),
--   $$
--
--   also written $R_f:=F^*$: conditioned on the current state $y$ of the stationary chain $X_0\sim\mu$, $X_{t+1}=f(X_t)$, the previous state is either inverse branch with probability $\tfrac12$.
--
--   Each inverse branch contracts distances by a factor $\tfrac12$; this backward contraction is the structural fact behind the horizon-uniform bounds.
--
--   **Formalization Note** Defined for every $y\in\mathbb R$; the paper uses $y\in[0,1]$.
-- source:
--   Huan, Risteski, Wei, Mitigating error propagation in chaotic dynamics via inference-time noising: a view from backward sampling, STOC 2027 submission (manuscript sha256 67925b3e946da20fbfc5ba5a928c6f5743bf4b2ee96e526e8e738f0494f558e6), eq. (2), p.3 and Definition 2.3, eq. (3), p.4 (PDF pp.3–4)

import Mathlib

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace TentNoise

/-- The reverse transition kernel of the tent map,
`F*(y, dx) = ½ δ_{a₀(y)}(dx) + ½ δ_{a₁(y)}(dx)` with inverse branches `a₀(y) = y/2`,
`a₁(y) = 1 − y/2` (Huan, Risteski, Wei, *Mitigating error propagation in chaotic dynamics via inference-time noising: a view from backward sampling*, STOC 2027 submission (manuscript sha256 67925b3e…), eq. (2), p.3 and eq. (3), p.4; also written `R_f := F*`).

**Formalization Note** Defined for every `y ∈ ℝ`; the paper uses `y ∈ [0, 1]`. -/
noncomputable def revTent : Kernel ℝ ℝ where
  toFun y := (2⁻¹ : ℝ≥0∞) • (Measure.dirac (y / 2) + Measure.dirac (1 - y / 2))
  measurable' := by
    refine Measure.measurable_of_measurable_coe _ (fun s hs => ?_)
    simp only [Measure.smul_apply, Measure.add_apply, Measure.dirac_apply' _ hs, smul_eq_mul]
    have h1 : Measurable (fun y : ℝ => s.indicator (1 : ℝ → ℝ≥0∞) (y / 2)) :=
      (measurable_one.indicator hs).comp (measurable_id.div_const 2)
    have h2 : Measurable (fun y : ℝ => s.indicator (1 : ℝ → ℝ≥0∞) (1 - y / 2)) :=
      (measurable_one.indicator hs).comp (measurable_const.sub (measurable_id.div_const 2))
    exact (h1.add h2).const_mul _

end TentNoise


