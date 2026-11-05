-- Prove2me | Definitions.Def_FractionalSpectralGP_multU
-- name    : FractionalSpectralGP_multU
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:22:53.861813+00:00
-- url     : https://prove2.me/theorems/b7fb20f6-7694-430e-97d9-1b9b3394e980
-- title:
--   The multiplication operator $M_u$ on $L^2(d\sigma)$
-- statement:
--   For a Borel measure $\sigma$ on $\mathbb R$ supported in $[-\tfrac12,\tfrac12]$, $M_u$ is the bounded operator on $L^2(d\sigma)$ of multiplication by the variable:
--
--   $$
--   (M_uf)(u)=u\,f(u).
--   $$
--
--   **Formalization Note** The multiplier used is the bounded continuous function $u\mapsto\max(-\tfrac12,\min(\tfrac12,u))$, which equals $u$ on $[-\tfrac12,\tfrac12]$; for every measure supported there (in particular every spectral setting) it agrees $\sigma$-a.e. with $u$, so the operator is exactly $M_u$. Off that class the definition is not used.
-- source:
--   Alpay, Jorgensen, Levanony, A class of Gaussian processes with fractional spectral measures, arXiv:1009.0233v1, §5, p.12

import Mathlib

open MeasureTheory Complex Filter Topology ProbabilityTheory
open scoped SchwartzMap ENNReal

namespace FractionalSpectralGP

/-- The operator `M_u` of multiplication by the variable `u` in `L²(dσ)`
(Alpay, Jorgensen, Levanony, arXiv:1009.0233v1, §5, p.12, before (5.1)), for a measure supported in `[-1/2, 1/2]`.

**Formalization Note.** The multiplier is the bounded continuous function
`u ↦ max (-1/2) (min (1/2) u)`, which equals `u` on `[-1/2, 1/2]`; for every measure of the
standing class (`SpectralSetting.support`) it is therefore `σ`-a.e. the variable `u`, and the
operator is multiplication by `u`. It is built with the Hölder product `L^∞ × L² → L²`. -/
noncomputable def multU (σ : Measure ℝ) : Lp ℂ 2 σ →L[ℂ] Lp ℂ 2 σ :=
  (ContinuousLinearMap.mul ℂ ℂ).holderL σ ⊤ 2 2
    ((memLp_top_of_bound (f := fun u : ℝ => ((max (-1/2 : ℝ) (min (1/2) u) : ℝ) : ℂ))
      (by fun_prop) (1/2) (ae_of_all _ fun u => by
        simp only [Complex.norm_real, Real.norm_eq_abs]
        rw [abs_le]; constructor
        · exact le_trans (by norm_num) (le_max_left _ _)
        · exact max_le (by norm_num) (min_le_left _ _))).toLp _)

end FractionalSpectralGP


