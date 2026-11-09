-- Prove2me | Definitions.Def_MetricMatchingDistortion_psAlloc
-- name    : MetricMatchingDistortion_psAlloc
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T17:16:35.477804+00:00
-- url     : https://prove2.me/theorems/846f33c8-40a4-4f9f-aed8-76b4102cd1a8
-- title:
--   Probabilistic Serial trajectory $X(t)$, remaining capacities $q_b(t)$, eaten items $b_a(t)$
-- statement:
--   Under **Probabilistic Serial** every item has capacity $1$ and, from $X(0)=0$, every agent eats her favorite item among those not yet exhausted at unit rate, switching when it runs out. $X(t)$ is the matrix after $t$ units of time ($X_{a,b}(t)$ is the amount of item $b$ agent $a$ has eaten), $q_b(t)=1-\sum_aX_{a,b}(t)$ is the fraction of item $b$ that remains, and for $t\in[0,1)$, $b_a(t)$ is the item agent $a$ eats just after time $t$: her favorite item with $q_b(t)>0$.
--
--   **Formalization Note** $X(t)$ runs the published eating step `ExAnteExPost.RPS.eatStep` (all agents eat until an item being eaten runs out or the time budget $t$ ends) $n+1$ times; each step but the last exhausts an item. Agents need $n\ge1$.
-- source:
--   Charikar, Haqi, Hastings, Huang, Ramakrishnan, Sublinear Metric Distortion for Matching, arXiv:2611.05777 (held version, sha256 fdf3452b105082d6ff680c8a762ec950298417efdebeb216b721705a9802e0da), Algorithm 7, p.46 (PDF p.48); §3.3, p.17 (PDF p.19); §6.2, p.51 (PDF p.53)

import Mathlib
import Definitions.Def_ExAnteExPost_RPS_Model
import Definitions.Def_MetricMatchingDistortion_Ranking

namespace MetricMatchingDistortion

open Finset

variable {n : ℕ}

/-- "Each agent a picks her favorite item among those not yet fully eaten" (Algorithm 7, p.46):
on a nonempty set `S` of items, agent `a` picks the item of `S` of least rank in her list. -/
def rankPick (rk : Ranking n) : ExAnteExPost.RPS.PickRule (Fin n) (Fin n) :=
  fun a S hS => (rk a).symm ((S.image (rk a)).min' (hS.image _))

/-- **The Probabilistic Serial trajectory `X(t)`.** Charikar et al., *Sublinear Metric Distortion
for Matching*, arXiv:2611.05777 (held version, sha256 fdf3452b…), Algorithm 7, p.46 (PDF p.48):
"Set t ← 0 and X(0) ← 0_{n×n}. Each item b initially has capacity 1, and is exhausted when
∑_a X_{a,b}(t) = 1. While t < 1: • Each agent a picks her favorite item b_a among those not yet
fully eaten. • All agents simultaneously eat their picked items at unit rate: for s ≥ t,
X_{a,b_a}(s) = X_{a,b_a}(t) + (s − t), with all other entries unchanged, until the first time t′ at
which some item is fully eaten (or t′ = 1). • Set t ← t′." §3.3, p.17: "Let X(t) denote the partial
fractional matching obtained by running PS for t units of time."

`psAlloc rk t` runs the eating protocol `ExAnteExPost.RPS.eatStep` (each step lets every agent eat
her favorite available item at rate one until an item being eaten runs out or the time budget
ends) with time budget `t`, from capacities `1` and the zero matrix, `n + 1` times.

**Formalization Note.** Every step but the last exhausts an item, so `n + 1` steps run the protocol
to the end of the budget and later steps change nothing. The trajectory is meant for
`t ∈ [0, 1]`; a nonpositive budget gives the zero matrix. `n ≥ 1` is the paper's standing
assumption (§2, p.9), carried as `[NeZero n]`. -/
noncomputable def psAlloc [NeZero n] (rk : Ranking n) (t : ℝ) : Fin n → Fin n → ℝ :=
  ((ExAnteExPost.RPS.eatStep (rankPick rk))^[n + 1] ⟨fun _ => 1, fun _ _ => 0, t⟩).X

/-- `q_b(t)`: "the fraction of item b that remains at time t" (§6.2, p.51 = PDF p.53),
`1 − ∑_a X_{a,b}(t)`. -/
noncomputable def remaining [NeZero n] (rk : Ranking n) (t : ℝ) (b : Fin n) : ℝ :=
  1 - ∑ a, psAlloc rk t a b

open Classical in
/-- `b_a(t)`: "the item that agent a eats just after time t, for t ∈ [0, 1)" (§6.2, p.51), i.e.
agent `a`'s favorite item among those with `q_b(t) > 0`. When no item remains (not the case for
`t < 1`) the value is the item with `a`'s own index. -/
noncomputable def eatenItem [NeZero n] (rk : Ranking n) (t : ℝ) (a : Fin n) : Fin n :=
  if h : (univ.filter fun b => 0 < remaining rk t b).Nonempty then
    rankPick rk a (univ.filter fun b => 0 < remaining rk t b) h
  else a

end MetricMatchingDistortion


