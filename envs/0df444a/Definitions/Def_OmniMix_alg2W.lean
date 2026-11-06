-- Prove2me | Definitions.Def_OmniMix_alg2W
-- name    : OmniMix_alg2W
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:41:01.237709+00:00
-- url     : https://prove2.me/theorems/12a29cf3-ee40-4a54-90e2-d801efeec713
-- title:
--   Weight density $W_{t,f}(v)$ of Algorithm 2
-- statement:
--   Algorithm 2 starts from $W_{1,f}(v)=1$ and updates
--   $$
--   W_{t+1,f}(v)=W_{t,f}(v)\exp\big(\eta z_{t,f,v}-\eta^2\,\mathbb E_{P\sim D_t}[P(1-P)b_v(P,f(x_t))^2]\big).
--   $$
--   In closed form, the weight before a round is the exponential of the sum of the update exponents of all earlier rounds.
--
--   **Formalization Note** Rounds are $0$-based: the weight at index $t$ uses the rounds $s<t$ (the paper's $W_{t+1}$), and equals $1$ at $t=0$.
-- source:
--   Liu–Luo–Ratliff, Omniprediction for All Mixable Proper Losses and Beyond, arXiv:2610.41023, Algorithm 2, p.15

import Mathlib
import Definitions.Def_OmniMix_alg2Reward
import Definitions.Def_OmniMix_alg2Var

namespace OmniMix

/-- **Weight density `W_{t,f}(v)` of Algorithm 2.** Liu–Luo–Ratliff, *Omniprediction for All Mixable Proper Losses and Beyond*, arXiv:2610.41023, Algorithm 2, p.15: "`W_{1,f}(v) = 1`" and
"`W_{t+1,f}(v) = W_{t,f}(v) exp(ηz_{t,f,v} − η²E_{P∼D_t}[P(1 − P)b_v(P, f(x_t))²])`".

**Formalization Note.** In closed form: `alg2W η x y D t f v` is the weight before the round of
0-based index `t` (the paper's `W_{t+1}`), the exponential of the sum of the update exponents of the
rounds `s < t`; at `t = 0` it is `1`. -/
noncomputable def alg2W {X : Type*} {T : ℕ} (η : ℝ) (x : Fin T → X) (y : Fin T → Bool)
    (D : Fin T → FinDist) (t : ℕ) (f : X → unitInterval) (v : ℝ) : ℝ :=
  Real.exp (∑ s ∈ Finset.univ.filter (fun s : Fin T => s.val < t),
    (η * alg2Reward x y D s f v - η ^ 2 * alg2Var x D s f v))

end OmniMix


