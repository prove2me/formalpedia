-- Prove2me | Definitions.Def_OmniMix_Supplement_alg1Phi
-- name    : OmniMix_Supplement_alg1Phi
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T08:35:04.402945+00:00
-- url     : https://prove2.me/theorems/043b63ae-34e9-42f0-a8da-511a19b2b5a0
-- title:
--   Total mass $\Phi_t$ of Algorithm 1
-- statement:
--   Algorithm 1 uses the prior $\pi_0=\mathrm{Unif}(F)\otimes\mu_0$ on experts, with $\mu_0$ the uniform distribution on $[0,1]$. The **total mass** before round $t$ is
--   $$
--   \Phi_t=\mathbb E_{(f,v)\sim\pi_0}[W_{t,f}(v)]=\frac1{|F|}\sum_{f\in F}\int_0^1W_{t,f}(v)\,dv.
--   $$
--
--   It normalizes the test function $G_t$.
-- source:
--   Liu–Luo–Ratliff, Omniprediction for All Mixable Proper Losses and Beyond, arXiv:2610.41023, Algorithm 1, p.11 (PDF p.13)

import Mathlib
import Definitions.Def_OmniMix_Supplement_alg1W

namespace OmniMix.Supplement

/-- **Total mass `Φ_t = E_{(f,v)∼π_0}[W_{t,f}(v)]` of Algorithm 1.** Liu–Luo–Ratliff,
*Omniprediction for All Mixable Proper Losses and Beyond*, arXiv:2610.41023, Algorithm 1, p.11:
"prior `π_0 = Unif(F) ⊗ µ_0`, where `µ_0` is uniform on `[0, 1]`".

**Formalization Note.** The expectation over `π_0` is written out as
`(1/|F|) Σ_{f∈F} ∫_0^1 W_{t,f}(v) dv` (Lebesgue measure on `[0,1]`); no product measure is needed.
The round index `t` is 0-based, as in `alg1W`. -/
noncomputable def alg1Phi {X : Type*} {T : ℕ} (F : Finset (X → unitInterval)) (η : ℝ)
    (x : Fin T → X) (y : Fin T → Bool) (D : Fin T → MeasureTheory.ProbabilityMeasure unitInterval)
    (t : ℕ) : ℝ :=
  (1 / (F.card : ℝ)) * ∑ f ∈ F, ∫ v in Set.Icc (0 : ℝ) 1, alg1W η x y D t f v

end OmniMix.Supplement


