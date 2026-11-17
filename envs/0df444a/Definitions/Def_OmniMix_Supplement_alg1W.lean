-- Prove2me | Definitions.Def_OmniMix_Supplement_alg1W
-- name    : OmniMix_Supplement_alg1W
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T08:34:27.249452+00:00
-- url     : https://prove2.me/theorems/ddf3bd8b-bbbe-4e55-a815-5963d6078257
-- title:
--   Weight density $W_{t,f}(v)$ of Algorithm 1
-- statement:
--   Algorithm 1 starts from $W_{1,f}(v)=1$ and updates, with learning rate $\eta$,
--   $$
--   W_{t+1,f}(v)=W_{t,f}(v)\exp\!\big(\eta z_{t,f,v}-\eta^2z_{t,f,v}^2\big),
--   $$
--   an exponential-weights update with a second-order correction by the squared reward. In closed form, $W_{t+1,f}(v)=\exp\big(\sum_{s\le t}(\eta z_{s,f,v}-\eta^2z_{s,f,v}^2)\big)$.
--
--   **Formalization Note** Rounds are $0$-based: the value at index $t$ is the weight before round $t$, built from rounds $s<t$, and equals $1$ at $t=0$.
-- source:
--   Liu–Luo–Ratliff, Omniprediction for All Mixable Proper Losses and Beyond, arXiv:2610.41023, Algorithm 1, p.11 (PDF p.13)

import Mathlib
import Definitions.Def_OmniMix_Supplement_alg1Reward

namespace OmniMix.Supplement

/-- **Weight density `W_{t,f}(v)` of Algorithm 1.** Liu–Luo–Ratliff, *Omniprediction for All
Mixable Proper Losses and Beyond*, arXiv:2610.41023, Algorithm 1, p.11: "`W_{1,f}(v) = 1`" and
"`W_{t+1,f}(v) = W_{t,f}(v) exp(ηz_{t,f,v} − η²z²_{t,f,v})`".

**Formalization Note.** In closed form: `alg1W η x y D t f v` is the weight before the round of
0-based index `t` (the paper's `W_{t+1}`), the exponential of the sum of the update exponents
`η z_{s,f,v} − η² z_{s,f,v}²` of the rounds `s < t`; at `t = 0` it is `1`. The correction is the
squared reward, not Algorithm 2's Bernoulli variance. -/
noncomputable def alg1W {X : Type*} {T : ℕ} (η : ℝ) (x : Fin T → X) (y : Fin T → Bool)
    (D : Fin T → MeasureTheory.ProbabilityMeasure unitInterval) (t : ℕ) (f : X → unitInterval)
    (v : ℝ) : ℝ :=
  Real.exp (∑ s ∈ Finset.univ.filter (fun s : Fin T => s.val < t),
    (η * alg1Reward x y D s f v - η ^ 2 * alg1Reward x y D s f v ^ 2))

end OmniMix.Supplement


