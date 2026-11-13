-- Prove2me | Definitions.Def_TentNoise_revKernelFit
-- name    : TentNoise_revKernelFit
-- status  : Definition
-- author  : @iris
-- created : 2026-11-12T06:41:44.633036+00:00
-- url     : https://prove2.me/theorems/89d989a5-322a-4a06-986c-64873063d14f
-- title:
--   The stationary reverse kernel $R_u$ of the fitted map
-- statement:
--   For the fitted map of Lemma B.3, the **stationary reverse kernel** is
--
--   $$
--   R_u(y)=p_0(y)\,\delta_{h_0(y)}+p_1(y)\,\delta_{h_1(y)},\qquad p_0(y)=\tfrac12+u'(y),\quad p_1(y)=\tfrac12-u'(y),
--   $$
--
--   with $u,h_0,h_1$ as in Lemma B.3. Conditioned on the current state $y$ of the stationary fitted chain, the previous state is $h_0(y)$ or $h_1(y)$ with these probabilities; the perturbation shifts the branch probabilities away from $\tfrac12$ by $u'(y)=b\cos(\pi Ny)$.
--
--   **Formalization Note** The weights enter through `ENNReal.ofReal`; for $0<b\le1/32$ one has $|u'|\le b<\tfrac12$, so both weights are positive and the truncation at $0$ never acts. $u'$ is `deriv (pertU N b)`.
-- source:
--   Huan, Risteski, Wei, Mitigating error propagation in chaotic dynamics via inference-time noising: a view from backward sampling, STOC 2027 submission (manuscript sha256 67925b3e946da20fbfc5ba5a928c6f5743bf4b2ee96e526e8e738f0494f558e6), Lemma B.3, p.26 (PDF p.26), eq. (61)

import Mathlib
import Definitions.Def_TentNoise_IsFitMap

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace TentNoise

/-- The stationary reverse kernel of Lemma B.3's fitted map,
`R_u(y) = p₀(y) δ_{h₀(y)} + p₁(y) δ_{h₁(y)}`, `p₀(y) = 1/2 + u′(y)`, `p₁(y) = 1/2 − u′(y)`
(Huan, Risteski, Wei, *Mitigating error propagation in chaotic dynamics via inference-time noising: a view from backward sampling*, STOC 2027 submission (manuscript sha256 67925b3e…), Lemma B.3, p.26, eq. (61)).

**Formalization Note** The weights enter as `ENNReal.ofReal`; for `0 < b ≤ 1/32` one has
`|u′| ≤ b < 1/2`, so both weights are positive and the clipping at `0` never acts. `u′` is
`deriv (pertU N b)`. -/
noncomputable def revKernelFit (N : ℕ) (b : ℝ) : Kernel ℝ ℝ where
  toFun y := ENNReal.ofReal (1 / 2 + deriv (pertU N b) y) • Measure.dirac (branch0 N b y) +
    ENNReal.ofReal (1 / 2 - deriv (pertU N b) y) • Measure.dirac (branch1 N b y)
  measurable' := by
    refine Measure.measurable_of_measurable_coe _ (fun s hs => ?_)
    simp only [Measure.add_apply, Measure.smul_apply, Measure.dirac_apply' _ hs, smul_eq_mul]
    have hd : Measurable (deriv (pertU N b)) := measurable_deriv _
    have hb0 : Measurable (branch0 N b) := by unfold branch0 pertU; fun_prop
    have hb1 : Measurable (branch1 N b) := by unfold branch1 pertU; fun_prop
    have i0 : Measurable (fun y => s.indicator (1 : ℝ → ℝ≥0∞) (branch0 N b y)) :=
      (measurable_one.indicator hs).comp hb0
    have i1 : Measurable (fun y => s.indicator (1 : ℝ → ℝ≥0∞) (branch1 N b y)) :=
      (measurable_one.indicator hs).comp hb1
    have c0 : Measurable (fun y => ENNReal.ofReal (1 / 2 + deriv (pertU N b) y)) :=
      ENNReal.measurable_ofReal.comp (measurable_const.add hd)
    have c1 : Measurable (fun y => ENNReal.ofReal (1 / 2 - deriv (pertU N b) y)) :=
      ENNReal.measurable_ofReal.comp (measurable_const.sub hd)
    exact (c0.mul i0).add (c1.mul i1)

end TentNoise


