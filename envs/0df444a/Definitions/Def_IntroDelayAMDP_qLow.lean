-- Prove2me | Definitions.Def_IntroDelayAMDP_qLow
-- name    : IntroDelayAMDP_qLow
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T05:46:48.113734+00:00
-- url     : https://prove2.me/theorems/33b587e8-5203-4d07-886a-9ac1e89e20e5
-- title:
--   Lower confidence occupancy
-- statement:
--   $q(s,a)=\min_{P'\in\mathcal P}q^{P',\pi}(s,a)$: the least occupancy of the pair $(s,a)$ under $\pi$ over a set $\mathcal P$ of transitions.
--
--   **Formalization Note** Written as a real infimum over the subtype of $\mathcal P$. For the confidence sets the set is nonempty and the values lie in $[0,1]$, so this is the genuine infimum; compactness gives attainment, which the statements do not use.
-- source:
--   Kulkarni–Nguyen–Chang–Dai, Introducing Feedback Delays to Non-Delayed Adversarial MDPs, STOC 2027 submission (manuscript sha256 a639c54c…5e3530), Algorithm 1, line 4, p.16; Section 3, p.15

import Mathlib
import Definitions.Def_IntroDelayAMDP_LayeredSpace
import Definitions.Def_IntroDelayAMDP_occ

namespace IntroDelayAMDP

/-- **Lower confidence occupancy** `q_k(s, a) = min_{P′∈P_k} q^{P′,π_k}(s, a)` (Algorithm 1,
line 4, p.16; Section 3, p.15). Kulkarni–Nguyen–Chang–Dai, *Introducing Feedback Delays to Non-Delayed Adversarial MDPs*, STOC 2027 submission (manuscript sha256 a639c54c…5e3530), printed p.15: "the lower confidence bound
`q_k(s, a) ≜ min_{P′∈P_k} q^{P′,π_k}(s, a)`".

For a set `cs` of transitions and a policy `π`, `qLow L cs π s a` is the infimum over `P′ ∈ cs` of
the occupancy `q^{P′,π}(s, a)`.

**Formalization Note.** Written as `⨅` over the subtype of `cs`. For the confidence sets of the
paper the set is nonempty and the occupancies of a policy lie in `[0, 1]`, so this is the genuine
infimum (it is attained by compactness, which the statements do not use). -/
noncomputable def qLow {St A : Type} [Fintype St] [DecidableEq St] [Fintype A] {H : ℕ}
    (L : LayeredSpace St H) (cs : Set (St → A → St → ℝ)) (π : St → A → ℝ) (s : St) (a : A) : ℝ :=
  ⨅ P' : cs, occ L (P' : St → A → St → ℝ) π s a

end IntroDelayAMDP


