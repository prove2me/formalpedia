-- Prove2me | Definitions.Def_IntroDelayAMDP_confSet
-- name    : IntroDelayAMDP_confSet
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T05:45:34.690516+00:00
-- url     : https://prove2.me/theorems/5e230d2d-5b4f-42a6-8a1c-5c384a6460dc
-- title:
--   Confidence set of transitions, Eq. (16)
-- statement:
--   For an observation record (for every pair, the list of next states observed after its visits), the **confidence set** is the set of transitions $P'$ such that for every pair whose constraints are satisfied by some distribution on the next layer, $P'(\cdot\mid s,a)$ satisfies them. If no distribution satisfies the constraints of a pair, they are dropped for that pair, so the set is never empty.
--
--   With the empty record it is the set of all transitions, as in Algorithm 1, line 1.
-- source:
--   Kulkarni–Nguyen–Chang–Dai, Introducing Feedback Delays to Non-Delayed Adversarial MDPs, STOC 2027 submission (manuscript sha256 a639c54c…5e3530), Eq. (16), pp.14–15

import Mathlib
import Definitions.Def_IntroDelayAMDP_LayeredSpace
import Definitions.Def_IntroDelayAMDP_IsTransition
import Definitions.Def_IntroDelayAMDP_pairConstr

namespace IntroDelayAMDP

/-- **Confidence set of transitions** `P_k` (Eq. (16), pp.14–15). Kulkarni–Nguyen–Chang–Dai, *Introducing Feedback Delays to Non-Delayed Adversarial MDPs*, STOC 2027 submission (manuscript sha256 a639c54c…5e3530), printed pp.14–15:
"`P_k ≜ {P′ | |P′(s′ | s, a) − P̂_n(s′ | s, a)| ≤ 2√(P̂_n(s′ | s, a)β/n) + 5β/n, ∀ 0 ≤ h < H,
(s, a, s′) ∈ S_h × A × S_{h+1}, 1 ≤ n ≤ N_k(s, a)}` (16) where, if no distribution in
`∆(S_{h+1})` satisfies all constraints of a pair `(s, a)`, we drop these constraints, so that
`P′(· | s, a)` can be any distribution and `P_k` is never empty."

For an observation record `obs` (for every pair `(s, a)`, the list of next states observed after
its visits, in order), `confSet L β obs` is the set of transitions `P′` (`IsTransition L P′`) such
that for every pair `(s, a)` whose constraints (`pairConstr`) are satisfied by **some**
distribution supported on the next layer, `P′(· | s, a)` satisfies them. The drop rule is per
pair.

**Formalization Note.** `N_k(s, a)` is the length of the pair's list. "The set of all
transitions" of Algorithm 1, line 1, is `confSet L β (fun _ _ => [])`. -/
def confSet {St A : Type} [Fintype St] [DecidableEq St] {H : ℕ} (L : LayeredSpace St H) (β : ℝ)
    (obs : St → A → List St) : Set (St → A → St → ℝ) :=
  {P' | IsTransition L P' ∧ ∀ s a,
    (∃ q : St → ℝ, (∀ s', 0 ≤ q s') ∧ (∀ s', q s' ≠ 0 → L.layer s' = L.layer s + 1) ∧
        ∑ s', q s' = 1 ∧ pairConstr L β (obs s a) (L.layer s) q) →
      pairConstr L β (obs s a) (L.layer s) (P' s a)}

end IntroDelayAMDP


