-- Prove2me | Definitions.Def_ShallowShadows_ShadowNorm_lsShadowNormSq
-- name    : ShallowShadows_ShadowNorm_lsShadowNormSq
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:32:31.323845+00:00
-- url     : https://prove2.me/theorems/8ce3afaf-61b7-4981-ba8a-476aa2fbda2f
-- title:
--   Locally scrambled squared shadow norm $\|O\|^2_{s,\mathrm{LS}}$ (Eq. (18))
-- statement:
--   For a finite ensemble $\mathcal U$, an operator $O$ and a state ensemble $\mathcal E$, the square of the **locally scrambled shadow norm** is the average of the state dependent squared shadow norm,
--
--   $$
--   \|O\|^2_{s,\mathrm{LS}} := \mathbb E_{\sigma\sim\mathcal E}\big[\|O\|^2_{s,\sigma}\big].
--   $$
--
--   The paper takes $\mathcal E$ a state one-design; Theorem 7 shows the value is then $\sum_\lambda \beta_\lambda^2/t_{\lambda,d}$, independent of $\mathcal E$.
--
--   **Formalization Note** The average is the Bochner integral against $\mathcal E$; the integrand is continuous and bounded on density operators.
-- source:
--   Bertoni, Haferkamp, Hinsche, Ioannou, Eisert, Pashayan, Shallow shadows: Expectation estimation using low-depth random Clifford circuits, arXiv:2209.12924v3, Eq. (18), p. 7

import Mathlib
import Definitions.Def_ShallowShadows_ShadowNorm_stateShadowNormSq
import Definitions.Def_ShallowShadows_ShadowNorm_IsStateOneDesign

open ClassicalShadow.Linear MeasureTheory

namespace ShallowShadows.ShadowNorm

/-- Bertoni, Haferkamp, Hinsche, Ioannou, Eisert, Pashayan, *Shallow shadows: Expectation
estimation using low-depth random Clifford circuits*, arXiv:2209.12924v3, Eq. (18), p. 7: the
square of the locally scrambled shadow norm `‖O‖²_{s,LS} := E_{σ∼ℰ}[‖O‖²_{s,σ}]`, the average of
the state dependent squared shadow norm over a state ensemble `ℰ`; the paper takes `ℰ` a state
one-design (`IsStateOneDesign`) and `𝒰 = 𝒰_d`.

**Formalization Note.** The average is the Bochner integral over the measure `ℰ` on density
operators. The integrand `σ ↦ ‖O‖²_{s,σ}` is continuous and bounded on density operators, hence
integrable under a probability measure. -/
noncomputable def lsShadowNormSq {n : ℕ} {ι : Type} [Fintype ι] (E : Primitive n ι) (O : Op n)
    (𝓔 : Measure {σ : Op n // WildeQIT.IsDensityOperator σ}) : ℝ :=
  ∫ σ, stateShadowNormSq E O σ.1 ∂𝓔

end ShallowShadows.ShadowNorm


