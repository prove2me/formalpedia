-- Prove2me | Definitions.Def_MobilePromo_phaseGap
-- name    : MobilePromo_phaseGap
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:19:51.885682+00:00
-- url     : https://prove2.me/theorems/a688b67f-e51f-4233-bae0-738ec10b1e93
-- title:
--   The expectations of (8): the phases $\mathcal A_{s_1}$ and $\mathcal A_{s_2}$
-- statement:
--   For a history $x$, $\mathcal A_{s_1}(x)$ (resp. $\mathcal A_{s_2}(x)$) is the collection of periods belonging to the exploration (resp. exploitation) phase of cycle $s$ in which there are active campaigns. This module defines the two expectations of (8), for BidAlloc $\hat\pi$ over $I$ seasons,
--
--   $$
--   \mathbb E\Bigl[\sum_{i=1}^I\sum_{t=1}^T\sum_{l}\mathbb 1\{\zeta_{i,t}=l\}\mathbb 1\{(i,t)\in\mathcal A\}\bigl(b^{\hat\pi}_{i,t,l}-b^*_{i,t,l}(\boldsymbol c_i(\hat X^{\hat\pi}_{i,t});\gamma^{(0)})\bigr)^2\Bigr],\qquad\mathcal A=\mathcal A_{s_1}\text{ or }\mathcal A_{s_2},
--   $$
--
--   and the event that the exploration phase of cycle $s$ has concluded within the horizon.
-- source:
--   Feng, Dawande, Janakiraman & Qi, An Asymptotically Tight Learning Algorithm for Mobile-Promotion Platforms, SSRN 3523491, pp.18–19, (8)

import Mathlib
import Definitions.Def_MobilePromo_bidAlloc

set_option autoImplicit false

namespace MobilePromo

/-- The exploration phase of cycle `s` has concluded by the phase state `st`. -/
def ExplorationDone {L : ℕ} (st : PhaseState L) (s : ℕ) : Prop :=
  s < st.s ∨ (s = st.s ∧ st.exploring = false)

/-- The next period after the history `h` is an active one lying in the exploration (`explore = true`)
or exploitation (`explore = false`) phase of cycle `s`: membership in `A_{s₁}`, resp. `A_{s₂}`
(SSRN 3523491, p.18). -/
def InPhase (M : Model) (X : Exploration M) {T : ℕ} (S : Schedule T) (s : ℕ) (explore : Bool)
    (h : List (Outcome M.L)) : Prop :=
  activeB S h = true ∧ (phaseOf X.k (activeB S) h).s = s ∧
    (phaseOf X.k (activeB S) h).exploring = explore

open Classical in
/-- The expectation of (8) for one phase of `BidAlloc` (SSRN 3523491, (8), p.19): for `explore = true`,
resp. `false`, it is
`E[∑_i ∑_t ∑_l 1{ζ_{i,t} = l} 1{(i,t) ∈ A} (b^π̂_{i,t,l} - b*_{i,t,l}(c_i(X̂^π̂_{i,t}); γ⁽⁰⁾))²]` with `A = A_{s₁}`, resp.
`A_{s₂}`, under `BidAlloc` over `I` seasons. -/
noncomputable def phaseGap (M : Model) (X : Exploration M) (mle : MLESelector M X) {T : ℕ}
    (S : Schedule T) (γ : M.ParamVec) (I s : ℕ) (explore : Bool) : ℝ :=
  pathExp M (bidAlloc M X mle S) γ (I * T) fun ω =>
    ∑ k : Fin (I * T), ∑ l,
      if (ω k).map Prod.fst = some l ∧ InPhase M X S s explore (pref ω k) then
        (bidAlloc M X mle S (pref ω k) l - bStarAt M S γ (pref ω k) l) ^ 2
      else 0

end MobilePromo


