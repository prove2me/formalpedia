-- Prove2me | Definitions.Def_CommissionsSubscriptions_InGammaU
-- name    : CommissionsSubscriptions_InGammaU
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T01:24:36.148982+00:00
-- url     : https://prove2.me/theorems/b0b81a31-7264-4381-af6e-e04ed0d26e96
-- title:
--   Feasible fees $(\gamma,\mu)\in\Gamma\times\mathcal U$
-- statement:
--   The pair $(\gamma,\mu)$ is **feasible**, $(\gamma,\mu)\in\Gamma\times\mathcal U$, if
--   $$\gamma^s_i\in[0,1],\qquad \gamma^b_j\ge0,\qquad \mu^s_i\ge0,\qquad \mu^b_j\ge0$$
--   for all seller types $i$ and buyer types $j$: commissions and subscriptions are nonnegative, and a seller commission is at most the whole price.
-- source:
--   Birge, Candogan, Chen, Saban, Optimal Commissions and Subscriptions in Networked Markets, SSRN abstract 3259716 (version of 2019-09-13), §2, p. 8 (definition of Γ and U)

import Mathlib
import Definitions.Def_CommissionsSubscriptions_Fees

namespace CommissionsSubscriptions

/-- **Feasible commissions and subscriptions, `(γ, µ) ∈ Γ × U`.**
Birge, Candogan, Chen, Saban, *Optimal Commissions and Subscriptions in Networked Markets*,
SSRN 3259716 (version of 2019-09-13), p. 8:
`Γ = {γ : γ^s_i ∈ [0,1], γ^b_j ∈ [0,∞)}` and `U = {µ : µ^s_i, µ^b_j ∈ [0,∞)}`. -/
def InGammaU {S B : Type} (f : Fees S B) : Prop :=
  (∀ i, f.gs i ∈ Set.Icc (0 : ℝ) 1) ∧ (∀ j, 0 ≤ f.gb j) ∧ (∀ i, 0 ≤ f.ms i) ∧ (∀ j, 0 ≤ f.mb j)

end CommissionsSubscriptions


