-- Prove2me | Definitions.Def_VehShare_SeqBounds_IsStationary
-- name    : VehShare_SeqBounds_IsStationary
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T03:38:19.971906+00:00
-- url     : https://prove2.me/theorems/42d5ca9a-bea8-4acd-8634-f652be55a457
-- title:
--   Stationary distribution of the chain under a policy
-- statement:
--   A function $\pi$ on the states is a **stationary distribution** of the chain under the policy $q$ if $\pi(x)\ge 0$, $\sum_x\pi(x)=1$ (p. 5) and $\pi Q=0$, written as
--
--   $$
--   \sum_x \pi(x)\,(Qf)(x)=0\qquad\text{for every } f:S\to\mathbb R.
--   $$
--
--   **Formalization Note** No irreducibility or uniqueness is bundled: a state-dependent policy can make the chain reducible (e.g. $q\equiv0$), and every stationary distribution counts.
-- source:
--   Benjaafar, Shen, Pricing in On-Demand (and One-Way) Vehicle Sharing Networks, SSRN 3998297 (version of 2023-01-10), https://ssrn.com/abstract=3998297, p. 5

import Mathlib
import Definitions.Def_VehShare_SeqBounds_Policy
import Definitions.Def_VehShare_SeqBounds_gen

namespace VehShare.SeqBounds

/-- **Stationary (steady-state) distribution of the chain under a policy.**
Benjaafar, Shen, *Pricing in On-Demand (and One-Way) Vehicle Sharing Networks*, SSRN 3998297
(version of 2023-01-10), p. 5: "We denote the steady state probability of the system being in state `x` by `π(x)` where
`π(x) ≥ 0` and `∑_{x∈S} π(x) = 1`."

`π` is a probability vector on the finite state space with `π Q = 0`, written as
`∑_z π(z) (Q f)(z) = 0` for every `f` (indicator functions give `π Q = 0`).

**Formalization Note.** Reading 2: no irreducibility or uniqueness is bundled; a state-dependent
policy can make the chain reducible (e.g. `q ≡ 0`), and every stationary distribution counts. -/
def IsStationary {P : Instance} {K : ℕ} (q : Policy P K) (π : State P K → ℝ) : Prop :=
  (∀ z, 0 ≤ π z) ∧ ∑ z, π z = 1 ∧ ∀ f : State P K → ℝ, ∑ z, π z * gen q.1 f z = 0

end VehShare.SeqBounds


