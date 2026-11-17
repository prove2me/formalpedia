-- Prove2me | Definitions.Def_OmniMix_Supplement_alg1G
-- name    : OmniMix_Supplement_alg1G
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T08:35:58.524684+00:00
-- url     : https://prove2.me/theorems/8b69ae99-1da5-42f7-a6e7-3633458e95c5
-- title:
--   Expected test function $G_t$ of Algorithm 1
-- statement:
--   The **expected test function** of round $t$ of Algorithm 1 is the mixture of threshold tests
--   $$
--   G_t(p)=\frac{\eta}{\Phi_t}\,\mathbb E_{(f,v)\sim\pi_0}\big[W_{t,f}(v)\,b_v(p,f(x_t))\big]=\frac{\eta}{\Phi_t}\cdot\frac1{|F|}\sum_{f\in F}\int_0^1W_{t,f}(v)\,b_v(p,f(x_t))\,dv .
--   $$
--
--   It depends on the forecasts and outcomes of earlier rounds and on the current context $x_t$ only; the forecast of round $t$ is chosen to make $G_t$ nearly unbiased (the EVI condition).
-- source:
--   Liu–Luo–Ratliff, Omniprediction for All Mixable Proper Losses and Beyond, arXiv:2610.41023, Algorithm 1, p.11 (PDF p.13), Eq. (17)

import Mathlib
import Definitions.Def_OmniMix_Supplement_alg1Phi

namespace OmniMix.Supplement

open OmniMix

/-- **Expected test function `G_t` of Algorithm 1.** Liu–Luo–Ratliff, *Omniprediction for All
Mixable Proper Losses and Beyond*, arXiv:2610.41023, Algorithm 1, p.11 and Eq. (17):
"`G_t(p) = (η/Φ_t) E_{(f,v)∼π_0}[W_{t,f}(v) b_v(p, f(x_t))]`".

**Formalization Note.** The expectation over `π_0 = Unif(F) ⊗ µ_0` is written out as in
`alg1Phi`. The round `t` is 0-based; `G_t` uses the weights built from rounds `s < t` and the
current context `x_t` only. `b_v` is the base `OmniMix.bV`. -/
noncomputable def alg1G {X : Type*} {T : ℕ} (F : Finset (X → unitInterval)) (η : ℝ)
    (x : Fin T → X) (y : Fin T → Bool) (D : Fin T → MeasureTheory.ProbabilityMeasure unitInterval)
    (t : Fin T) (p : ℝ) : ℝ :=
  (η / alg1Phi F η x y D t.val) * ((1 / (F.card : ℝ)) * ∑ f ∈ F, ∫ v in Set.Icc (0 : ℝ) 1,
    alg1W η x y D t.val f v * bV v p (f (x t)))

end OmniMix.Supplement


