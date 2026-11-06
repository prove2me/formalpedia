-- Prove2me | Definitions.Def_OmniMix_alg2Phi
-- name    : OmniMix_alg2Phi
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:42:16.372778+00:00
-- url     : https://prove2.me/theorems/b207e281-1d12-4230-899b-553abc17683c
-- title:
--   Total mass $\Phi_t$ of Algorithm 2
-- statement:
--   With the prior $\pi_\delta=\mathrm{Unif}(F)\otimes\mu_\delta$, $\mu_\delta(dv)=dv/(M_\delta v(1-v))$ on $I_\delta$ (Eq. (21)),
--   $$
--   \Phi_t=\mathbb E_{(f,v)\sim\pi_\delta}[W_{t,f}(v)]=\frac1{|F|}\sum_{f\in F}\int_{I_\delta}\frac{W_{t,f}(v)}{M_\delta\,v(1-v)}\,dv,
--   $$
--   with $\delta=1/(2(T+1))$ and $M_\delta=2\log(2T+1)$.
-- source:
--   Liu–Luo–Ratliff, Omniprediction for All Mixable Proper Losses and Beyond, arXiv:2610.41023, Algorithm 2, p.15 and Eq. (21), p.13

import Mathlib
import Definitions.Def_OmniMix_alg2W
import Definitions.Def_OmniMix_deltaT
import Definitions.Def_OmniMix_Mdelta
import Definitions.Def_OmniMix_Idelta

namespace OmniMix

/-- **Total mass `Φ_t = E_{(f,v)∼π_δ}[W_{t,f}(v)]` of Algorithm 2.** Liu–Luo–Ratliff, *Omniprediction for All Mixable Proper Losses and Beyond*, arXiv:2610.41023, Algorithm 2, p.15,
with the prior `π_δ = Unif(F) ⊗ μ_δ`, `μ_δ(dv) = dv/(M_δ v(1 − v))` on `I_δ` (Eq. (21), p.13).

**Formalization Note.** The expectation over `π_δ` is written out as
`(1/|F|) Σ_{f∈F} ∫_{I_δ} W_{t,f}(v) dv/(M_δ v(1−v))`, with `δ = deltaT T`, `M_δ = Mdelta T`; no
product measure is needed. The round index `t` is 0-based, as in `alg2W`. -/
noncomputable def alg2Phi {X : Type*} (F : Finset (X → unitInterval)) (T : ℕ) (η : ℝ)
    (x : Fin T → X) (y : Fin T → Bool) (D : Fin T → FinDist) (t : ℕ) : ℝ :=
  (1 / (F.card : ℝ)) * ∑ f ∈ F, ∫ v in Idelta (deltaT T),
    alg2W η x y D t f v / (Mdelta T * (v * (1 - v)))

end OmniMix


