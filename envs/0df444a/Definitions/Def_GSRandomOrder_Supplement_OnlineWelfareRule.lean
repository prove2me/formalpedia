-- Prove2me | Definitions.Def_GSRandomOrder_Supplement_OnlineWelfareRule
-- name    : GSRandomOrder_Supplement_OnlineWelfareRule
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T08:10:14.120645+00:00
-- url     : https://prove2.me/theorems/3602ce04-71cd-4a44-a1e4-89b299f062d0
-- title:
--   Online welfare algorithm and the represented and oracle observation models
-- statement:
--   In the welfare problem every arriving item must be given to one bidder or discarded, irrevocably. An **online welfare algorithm** decides, at the arrival of $g_k$, an action in $\{\text{bidder }1,\dots,\text{bidder }m,\text{discard}\}$ at random, as a function of what it has observed so far and of its own earlier actions. It is described by the probabilities of each action given the observation and the earlier actions; given the order $\sigma$, an action sequence $D$ has probability $\prod_j \mathrm{prob}(\text{observation after } j+1 \text{ arrivals},\,D_{<j})(D_j)$. Bidder $i$'s bundle after $t$ arrivals is $\{g_{j+1}: j<t,\ D_j=i\}$.
--
--   Two observation models (Appendix E):
--
--   1. **Oracle model.** After $k$ arrivals the algorithm knows the labels $g_1,\dots,g_k$ and the values $v_i(T)$ of every bidder on every set $T\subseteq S_k$ of arrived items.
--   2. **Represented model.** In addition, it knows the vectors $u_{ig}$ of every bidder $i$ for the arrived items $g\in S_k$; vectors of unarrived items are not known.
--
--   **Formalization Note** The information restriction is structural: the algorithm's input type contains only the observation (labels, masked values, masked vectors) and its earlier actions. Behavioural rules have exactly the joint laws of randomized online algorithms with perfect recall (Kuhn's theorem).
-- source:
--   Paes Leme, Pál, Patel, Gross Substitutes Welfare in Random Order, STOC 2027 submission (manuscript sha256 69787f50…), §1, p.3 ("Welfare"); App. E, pp.31–32 (represented model, oracle model)

import Mathlib
import Definitions.Def_GSRandomOrder_Supplement_prefixSet

set_option autoImplicit false

namespace GSRandomOrder.Supplement

/-- **Online welfare algorithm** (R. Paes Leme, M. Pál, N. Patel, *Gross Substitutes Welfare in
Random Order*, STOC 2027 submission, manuscript sha256 69787f50…, §1, p.3 "Welfare"; App. E,
pp.31–32): at the arrival of `g_k` the algorithm gives `g_k` to one bidder (`some i`) or discards
it (`none`), irrevocably, as a randomized function of what it has observed so far and of its own
earlier decisions.

The algorithm is given by its behavioural rule: `prob o ds a` is the probability of action `a`
when `o` is the observation after the `k`-th arrival and `ds = [a_1, …, a_{k−1}]` its earlier
actions; for every input these probabilities form a distribution on `Option (Fin m)`.

**Formalization Note.** The information restriction is structural: the rule's input is only the
observation `o : Obs` (for the two models of App. E, the labels of the arrived items and the data
revealed on them, see `valueObs` and `vectorObs`) and its own past actions, never the instance.
Every randomized online algorithm with perfect recall has a behavioural rule with the same joint
law of (order, actions) (Kuhn's theorem), and conversely every behavioural rule is such an
algorithm, so the class is exactly the paper's. -/
structure OnlineWelfareRule (Obs : Type*) (m : ℕ) where
  /-- Probability of action `a` given the observation and the earlier actions. -/
  prob : Obs → List (Option (Fin m)) → Option (Fin m) → ℝ
  prob_nonneg : ∀ o ds a, 0 ≤ prob o ds a
  prob_sum : ∀ o ds, ∑ a, prob o ds a = 1

/-- The probability that the actions are `D` (`D j` = action on the arrival at position `j`)
when the observation after the first `t` arrivals is `obs t`:
`Π_j prob (obs (j + 1)) [D_0, …, D_{j−1}] (D_j)`. -/
def OnlineWelfareRule.weight {Obs : Type*} {n m : ℕ} (R : OnlineWelfareRule Obs m)
    (obs : ℕ → Obs) (D : Fin n → Option (Fin m)) : ℝ :=
  ∏ j : Fin n, R.prob (obs (j.val + 1)) (decisionList D j.val) (D j)

/-- Bidder `i`'s bundle after the first `t` arrivals, under the order `σ` and actions `D`:
`{g_{j+1} : j < t, D_j = some i}`. With `t = n` it is the final bundle `A_i`. -/
def bundleAt {n m : ℕ} (σ : Fin n ≃ Fin n) (D : Fin n → Option (Fin m)) (i : Fin m) (t : ℕ) :
    Finset (Fin n) :=
  (Finset.univ.filter fun j : Fin n => j.val < t ∧ D j = some i).image σ

/-- The value data observed on the arrived set `S`: the values `v_i(T)` of every bidder `i` on
every set `T ⊆ S` of arrived items (value queries), and nothing on the other sets (`⊥` there,
which carries no information since `S` is known from the labels). -/
def valueObs {n m : ℕ} (v : Fin m → Finset (Fin n) → WithBot ℝ) (S : Finset (Fin n)) :
    Fin m → Finset (Fin n) → WithBot ℝ :=
  fun i T => if T ⊆ S then v i T else ⊥

/-- The vectors observed on the arrived set `S` in the represented model: `u_{ig}` for every
bidder `i` and every arrived item `g ∈ S`, nothing (`none`) for unarrived items. -/
def vectorObs {n m : ℕ} {F : Fin m → Type*} {d : Fin m → ℕ}
    (u : (i : Fin m) → Fin n → Fin (d i) → F i) (S : Finset (Fin n)) :
    (i : Fin m) → Fin n → Option (Fin (d i) → F i) :=
  fun i g => if g ∈ S then some (u i g) else none

end GSRandomOrder.Supplement


