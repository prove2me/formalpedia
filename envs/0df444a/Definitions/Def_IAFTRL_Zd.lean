-- Prove2me | Definitions.Def_IAFTRL_Zd
-- name    : IAFTRL_Zd
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:45:35.394263+00:00
-- url     : https://prove2.me/theorems/b1bb9c3a-50b5-4b5d-96ba-8cf26dbaebb8
-- title:
--   Estimated cumulative loss difference $Z_{t,a}$
-- statement:
--   The **estimated cumulative loss difference** of action $a$ at round $t$ is
--   $$
--   Z_{t,a}=\hat L_{t-1,a}-\hat L_{t-1,r_t}\ \ (\ge 0),
--   $$
--   the gap between the cumulative estimated loss of $a$ and that of the reference action $r_t$; here $\hat L_{t-1,a}=a^\top\sum_{s<t}\hat\theta_s$.
-- source:
--   Zhao–Tan, Best-of-Both-Worlds FTRL for Linear Bandits, arXiv:2611.01299, Section 2.1, p.17, Eq. (2.2)

import Mathlib
import Definitions.Def_IAFTRL_refArm

namespace IAFTRL

open Matrix

/-- **Estimated cumulative loss difference `Z_{t,a}`.** Zhao–Tan, *Best-of-Both-Worlds FTRL for Linear Bandits*, arXiv:2611.01299, Section 2.1, p.17, Eq. (2.2):
"`Z_{t,a} = L̂_{t−1,a} − L̂_{t−1,r_t}`. The nonnegative `Z_{t,a}` is the estimated cumulative loss
difference".

`Zd arms S a = ⟨arms a, S⟩ − ⟨r_t, S⟩` with `r_t = refArm arms S` and `S = Σ_{s<t} θ̂_s`. -/
noncomputable def Zd {d K : ℕ} (arms : Fin K → Fin d → ℝ) (S : Fin d → ℝ) (a : Fin K) : ℝ :=
  arms a ⬝ᵥ S - refArm arms S ⬝ᵥ S

end IAFTRL


