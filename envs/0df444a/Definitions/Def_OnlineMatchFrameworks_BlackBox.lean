-- Prove2me | Definitions.Def_OnlineMatchFrameworks_BlackBox
-- name    : OnlineMatchFrameworks_BlackBox
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T05:31:01.269204+00:00
-- url     : https://prove2.me/theorems/45c3dff8-8c53-4280-bf15-696106f560ac
-- title:
--   $\kappa$-approximate black box $\textsc{StarBB}$ and Algorithm 1, $\mathrm{ALG}(G)$
-- statement:
--   A black box assigns to each available set $A$ and customer $v$ a probability distribution over policies. It is **$\kappa$-approximate** if it plays only items of $A$ and
--   $$
--   \kappa\,\mathrm{OPT}(A,v)\le\sum_l \mathrm{BB}(A,v)(l)\,\mathrm{star}_v(l)\quad\text{for all }A,v.
--   $$
--   Algorithm 1 runs the black box on the items still available as each customer arrives. Offering a list $l$ when $A$ is available has continuation value
--   $$
--   \mathrm{step}_v(l,f)(A)=\sum_i\mathrm{mp}_v(l,i)\bigl(w_{l_i}+f(A\setminus\{l_i\})\bigr)+\Bigl(1-\sum_i\mathrm{mp}_v(l,i)\Bigr)f(A),
--   $$
--   and the expected reward is given by $\mathrm{alg}([\,],A)=0$ and $\mathrm{alg}(v::vs,A)=\sum_l\mathrm{BB}(A,v)(l)\,\mathrm{step}_v(l,\mathrm{alg}(vs,\cdot))(A)$. Finally $\mathrm{ALG}(G)=\mathrm{alg}(\text{order},U)$ for an arrival order.
--
--   **Formalization Note** The weight form of $\kappa$-approximation on p.5 implies the form above, which is the one the proof on p.40 uses. A randomized star policy is a mixture of lists, including simulated probes.
-- source:
--   Brubach, Grammel, Ma & Srinivasan, Online Matching Frameworks under Stochastic Rewards, Product Ranking, and Unknown Patience, arXiv:1907.03963v6, p.5; §4.1, Algorithm 1, p.14; §3, pp.11–12

import Definitions.Def_OnlineMatchFrameworks_StarPolicy

open scoped BigOperators

namespace OnlineMatchFrameworks

variable {U V : Type*} [DecidableEq U] [Fintype U]

/-- **The black box only offers available items.** arXiv:1907.03963v6, p.14: on the available set
`A` and customer `v`, `StarBB` plays a random policy whose items all lie in `A`. -/
def IsAvailableBlackBox (BB : Finset U → V → PMF (Policy U)) : Prop :=
  ∀ A v (l : Policy U), BB A v l ≠ 0 → ∀ u ∈ l.1, u ∈ A

namespace Instance

/-- **κ-approximate black box `StarBB`.** arXiv:1907.03963v6, p.5 and p.14; `StarBB` is "within a
constant factor κ of optimal". For every available set `A` and customer `v`, the black box's policy
uses only items of `A` and its expected reward is at least `κ · OPT(A, v)`.

**Formalization Note.** This is the form the proof uses (p.40). The form of p.5 (any weights) implies
it: set the weights to `0` outside `A` and delete those items from the returned list, which by
`Instance.surv_mono` cannot lower the reward. A randomized star policy is a mixture of lists,
including simulated probes, since a simulated failure is internal randomness; hence `PMF (Policy U)`. -/
def IsKappaApprox (G : Instance U V) (κ : ℝ) (BB : Finset U → V → PMF (Policy U)) : Prop :=
  IsAvailableBlackBox BB ∧
    ∀ A v, κ * G.starOpt A v ≤ ∑ l : Policy U, (BB A v l).toReal * G.starValue v l.1

/-- **One customer's step.** arXiv:1907.03963v6, §3, pp.11–12: offer the list `l` to `v` when `A` is
available. With probability `mp_v(l,i)` item `l_i` is sold, which earns `w_{l_i}` and removes it; with
the remaining probability nothing is sold. `f` is the value of the continuation. -/
def step (G : Instance U V) (v : V) (l : List U) (f : Finset U → ℝ) (A : Finset U) : ℝ :=
  ∑ i : Fin l.length, G.matchProb v l i * (G.w (l.get i) + f (A.erase (l.get i))) +
    (1 - ∑ i : Fin l.length, G.matchProb v l i) * f A

/-- **Expected reward of Algorithm 1 from a given state.** arXiv:1907.03963v6, Algorithm 1, p.14,
`AdvGreedy`: for each arriving vertex run `StarBB` on the available set. `algFrom BB vs A` is the
expected reward collected from the customers `vs`, in that order, when `A` is available.

**Formalization Note.** This is the recursion of total expectation over the process of pp.2, 11: edge
coins and patience are independent across customers and of the past, and the black box draws a fresh
policy at every arrival. -/
noncomputable def algFrom (G : Instance U V) (BB : Finset U → V → PMF (Policy U)) :
    List V → Finset U → ℝ
  | [], _ => 0
  | v :: vs, A => ∑ l : Policy U, (BB A v l).toReal * G.step v l.1 (G.algFrom BB vs) A

/-- **`ALG(G)`.** arXiv:1907.03963v6, p.12 and p.14: the expected reward of Algorithm 1 when the
customers arrive in the given order and all items start available. -/
noncomputable def ALG (G : Instance U V) (BB : Finset U → V → PMF (Policy U)) (order : List V) : ℝ :=
  G.algFrom BB order Finset.univ

end Instance

end OnlineMatchFrameworks


