-- Prove2me | Definitions.Def_OmniMix_alg2G
-- name    : OmniMix_alg2G
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:43:43.557439+00:00
-- url     : https://prove2.me/theorems/c4377a6f-1186-4dab-b83f-446b998be03d
-- title:
--   Expected test function $G_t$ of Algorithm 2
-- statement:
--   $$
--   G_t(p)=\frac1{\Phi_t}\,\mathbb E_{(f,v)\sim\pi_\delta}\big[W_{t,f}(v)\,\tilde b^\eta_v(p,f(x_t))\big]
--   =\frac1{\Phi_t}\cdot\frac1{|F|}\sum_{f\in F}\int_{I_\delta}\frac{W_{t,f}(v)\,\tilde b^\eta_v(p,f(x_t))}{M_\delta\,v(1-v)}\,dv .
--   $$
--   It depends only on the forecasts, contexts and outcomes of earlier rounds and on the current context.
-- source:
--   Liu–Luo–Ratliff, Omniprediction for All Mixable Proper Losses and Beyond, arXiv:2610.41023, §3.2, p.14, Eq. (25)

import Mathlib
import Definitions.Def_OmniMix_alg2Phi
import Definitions.Def_OmniMix_btilde

namespace OmniMix

/-- **Expected test function `G_t` of Algorithm 2.** Liu–Luo–Ratliff, *Omniprediction for All Mixable Proper Losses and Beyond*, arXiv:2610.41023, §3.2, p.14, Eq. (25):
"`G_t(p) = (1/Φ_t) E_{(f,v)∼π_δ}[W_{t,f}(v) b̃^η_v(p, f(x_t))]`".

**Formalization Note.** The expectation over `π_δ = Unif(F) ⊗ μ_δ` is written out as in `alg2Phi`.
The round `t` is 0-based; `G_t` uses the weights built from rounds `s < t` and the current context
`x_t` only. -/
noncomputable def alg2G {X : Type*} (F : Finset (X → unitInterval)) (T : ℕ) (η : ℝ)
    (x : Fin T → X) (y : Fin T → Bool) (D : Fin T → FinDist) (t : Fin T) (p : ℝ) : ℝ :=
  (1 / alg2Phi F T η x y D t.val) * ((1 / (F.card : ℝ)) * ∑ f ∈ F, ∫ v in Idelta (deltaT T),
    alg2W η x y D t.val f v * btilde η v p (f (x t)) / (Mdelta T * (v * (1 - v))))

end OmniMix


