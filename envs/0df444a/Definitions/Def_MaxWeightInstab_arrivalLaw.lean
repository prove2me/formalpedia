-- Prove2me | Definitions.Def_MaxWeightInstab_arrivalLaw
-- name    : MaxWeightInstab_arrivalLaw
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:12:40.69856+00:00
-- url     : https://prove2.me/theorems/eccba8f3-1b2e-4007-9b98-70324f520fb2
-- title:
--   Law of the external arrivals: independent Bernoulli$(a/J)$
-- statement:
--   In each time unit, each of the $2J$ externally fed queues receives one arrival with probability $a/J$ and none otherwise, independently of the other queues. Each end of the network thus receives jobs at rate $a$, spread over its $J$ queues, matching the traffic intensity (2), and "the number of external arrivals at different queues are assumed to be independent of each other" (p.5).
--
--   **Formalization Note** The success probability is $\min(\max(a/J,0),1)$ so that the law is defined for every real $a$; under the paper's assumptions $0<a<1\le J$ it equals $a/J$.
-- source:
--   Bramson, D'Auria, Walton, Stability and Instability of the MaxWeight Policy, arXiv:1909.10825v2, p.3 and p.5

import Mathlib
import Definitions.Def_MaxWeightInstab_ExtArrivals

namespace MaxWeightInstab

/-- The law of the external arrivals of one time unit (Bramson, D'Auria & Walton, *Stability and Instability of the MaxWeight Policy*, arXiv:1909.10825v2, pp.3 and 5): each of the `2J`
external queues `𝒜₁, …, 𝒜_J, ℬ₁, …, ℬ_J` receives one arrival with probability `a/J` and none
otherwise, independently of the other queues ("The number of external arrivals at different queues
are assumed to be independent of each other", p.5). With rate `a` at each end of the network, each
queue has mean `a/J`, as in (2).

**Formalization Note.** The success probability is `min (max (a/J) 0) 1`, so the law is defined for
every real `a`; under the paper's assumptions `0 < a < 1 ≤ J` it is exactly `a/J`. -/
noncomputable def arrivalLaw (a : ℝ) (J : ℕ) : PMF (ExtArrivals J) :=
  PMF.ofFintype
    (fun e => ∏ k, if e k then ((min (Real.toNNReal (a / J)) 1 : NNReal) : ENNReal)
      else 1 - ((min (Real.toNNReal (a / J)) 1 : NNReal) : ENNReal))
    (by
      rw [← Fintype.prod_sum (fun (_ : Fin J ⊕ Fin J) (b : Bool) =>
        if b then ((min (Real.toNNReal (a / J)) 1 : NNReal) : ENNReal)
        else 1 - ((min (Real.toNNReal (a / J)) 1 : NNReal) : ENNReal))]
      have hp : ((min (Real.toNNReal (a / J)) 1 : NNReal) : ENNReal) ≤ 1 := by
        exact_mod_cast min_le_right _ _
      simp only [Fintype.sum_bool, if_true, Bool.false_eq_true, if_false,
        add_tsub_cancel_of_le hp, Finset.prod_const_one])

end MaxWeightInstab


