-- Prove2me | Definitions.Def_StochAutoreg_bernPMF
-- name    : StochAutoreg_bernPMF
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:13:27.531068+00:00
-- url     : https://prove2.me/theorems/145bf821-2a94-49d7-88be-d8dcfd75a80b
-- title:
--   The law $\mathrm{Bern}(p)$ on $\{0,1\}$
-- statement:
--   The Bernoulli law on $\{0,1\}$ of mean $p\in[0,1]$, as a probability mass function.
-- source:
--   Doron-Arad–Mehalel–Mossel, Stochastic Autoregressive Learning, arXiv:2608.07224, §1.1, pp.2–3

import Mathlib
import Definitions.Def_StochAutoreg_bernMass

namespace StochAutoreg

/-- The law `Bern(p)` on `{0,1}`, for `p ∈ [0,1]`. Doron-Arad–Mehalel–Mossel, *Stochastic Autoregressive Learning*, arXiv:2608.07224, §1.1, pp.2–3. -/
noncomputable def bernPMF (p : unitInterval) : PMF Bool :=
  PMF.ofFintype (fun b => ENNReal.ofReal (bernMass p b)) (by
    have h0 : (0 : ℝ) ≤ p := p.2.1
    have h1 : (0 : ℝ) ≤ 1 - p := sub_nonneg.2 p.2.2
    simp [bernMass, ← ENNReal.ofReal_add h0 h1])

end StochAutoreg


