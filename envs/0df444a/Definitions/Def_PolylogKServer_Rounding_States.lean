-- Prove2me | Definitions.Def_PolylogKServer_Rounding_States
-- name    : PolylogKServer_Rounding_States
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T05:48:53.097861+00:00
-- url     : https://prove2.me/theorems/a11a44c2-5899-4c3b-85fb-2752ec6d0a92
-- title:
--   Randomized k-server states on HST leaves: consistency, balance, balance gap G(S, x), transport cost
-- statement:
--   Let $T$ be a rooted weighted tree whose leaves are the points of a finite metric space $M$.
--
--   1. A **configuration** is a set $C$ of exactly $k$ leaves. A **k-server state** $S$ is a probability distribution $\mu_S$ on configurations.
--   2. $S$ is **consistent** with a fractional state $x$ if its marginals are $x$:
--   $$
--   \sum_{C:\,i\in C}\mu_S(C)=x_i\qquad\text{for each leaf } i. \tag{55}
--   $$
--   3. For a node $p$, let $x_p=\sum_{i\in T(p)}x_i$ and $n_p(C)=|C\cap T(p)|$. A configuration $C$ is **balanced** with respect to $x$ if $n_p(C)\in\{\lfloor x_p\rfloor,\lceil x_p\rceil\}$ for every node $p$; a state $S$ is balanced if every configuration in its support is.
--   4. The **balance gap** of $S$ with respect to $x$ is
--   $$
--   G(S,x)=\sum_p W(p)\sum_C\mu_S(C)\,\min\big(|n_p(C)-\lfloor x_p\rfloor|,\ |n_p(C)-\lceil x_p\rceil|\big). \tag{57}
--   $$
--   5. The **cost of changing** $S$ to $S'$ is the transportation (earthmover) cost: the minimum over couplings $q$ of $\mu_S$ and $\mu_{S'}$ of $\sum_{C,C'}q(C,C')\,m(C,C')$, where $m(C,C')$ is the cost of a minimum-cost perfect matching between the $k$ points of $C$ and the $k$ points of $C'$ in $M$.
--
--   These notions carry the paper's online rounding of fractional k-server solutions on σ-HSTs (§5.2).
--
--   **Formalization Note** The paper does not define the cost of changing a state; the transportation cost above is the convention adopted, matching its remark that the fractional movement cost is an earthmover distance (p. 36). In (57) the sum runs over non-root nodes (the root has no edge to a parent; for consistent states its term would vanish). States are represented by real mass functions that are non-negative and sum to $1$.
-- source:
--   Bansal, Buchbinder, Mądry, Naor, A Polylogarithmic-Competitive Algorithm for the k-Server Problem, arXiv:1110.1580v1, pp. 36–37, §5.2 (configurations, states, consistency (55), balanced configurations and states (56), balance gap (57))

import Mathlib
import Definitions.Def_PolylogKServer_HST_Tree

/-!
# Randomized k-server states on the leaves of an HST

Bansal, Buchbinder, Mądry, Naor, *A Polylogarithmic-Competitive Algorithm for the k-Server
Problem*, arXiv:1110.1580v1, §5.2, pp. 36–37: configurations (k-subsets of the leaves),
k-server states (probability distributions on configurations), consistency (55), balanced
configurations and states (56), and the balance gap `G(S, x)` (57).

The leaves of `T` are the points of a finite metric space `M` through `e : M ≃ T.Leaf`.
The paper does not define "the cost of changing state `S` to `S′`"; it is taken here to be the
transportation (earthmover) cost between the two distributions, where moving from a
configuration `C` to a configuration `C′` costs the minimum-cost perfect matching of the two
`k`-subsets in the metric of `M`.
-/

namespace PolylogKServer.Rounding

open Finset PolylogKServer.HST

/-- A configuration: a subset of the leaves of size exactly `k` (p. 36). -/
abbrev KConfig (k : ℕ) (M : Type) := {C : Finset M // C.card = k}

/-- A k-server state (p. 36): a probability distribution `μ_S` on configurations, given by its
mass function. -/
def IsKState {k : ℕ} {M : Type} [Fintype M] [DecidableEq M] (S : KConfig k M → ℝ) : Prop :=
  (∀ C, 0 ≤ S C) ∧ ∑ C, S C = 1

/-- The point-mass k-server state at the configuration `C`. -/
def pureState {k : ℕ} {M : Type} [DecidableEq M] (C : KConfig k M) : KConfig k M → ℝ :=
  fun C' => if C' = C then 1 else 0

/-- Consistency (55), p. 36: `∑_{C ∋ i} μ_S(C) = x_i` for every leaf `i`. -/
def Consistent {k : ℕ} {M : Type} [Fintype M] [DecidableEq M] (S : KConfig k M → ℝ)
    (x : M → ℝ) : Prop :=
  ∀ i : M, ∑ C ∈ univ.filter (fun C : KConfig k M => i ∈ C.1), S C = x i

variable {V : Type} [Fintype V] [DecidableEq V]

/-- `x_p = ∑_{i ∈ T(p)} x_i`, the fractional amount of servers on the leaves below `p`. -/
noncomputable def massBelow (T : WTree V) {M : Type} [Fintype M] (e : M ≃ T.Leaf)
    (x : M → ℝ) (p : V) : ℝ := by
  classical
  exact ∑ m, if T.IsAnc p (e m : V) then x m else 0

/-- `n_p(C) = |C ∩ T(p)|`, the number of servers of the configuration `C` on leaves below `p`. -/
noncomputable def countBelow (T : WTree V) {M : Type} (e : M ≃ T.Leaf) (C : Finset M)
    (p : V) : ℕ := by
  classical
  exact (C.filter fun m => T.IsAnc p (e m : V)).card

/-- A configuration `C` is balanced with respect to `x` (p. 36): `n_p(C) ∈ {⌊x_p⌋, ⌈x_p⌉}` for
every node `p`. -/
def ConfigBalanced (T : WTree V) {M : Type} [Fintype M] (e : M ≃ T.Leaf) (x : M → ℝ)
    (C : Finset M) : Prop :=
  ∀ p : V, (countBelow T e C p : ℤ) = ⌊massBelow T e x p⌋ ∨
    (countBelow T e C p : ℤ) = ⌈massBelow T e x p⌉

/-- A k-server state is balanced with respect to `x` (p. 36–37, (56)): every configuration in
its support is balanced with respect to `x`. -/
def Balanced (T : WTree V) {k : ℕ} {M : Type} [Fintype M] [DecidableEq M] (e : M ≃ T.Leaf)
    (x : M → ℝ) (S : KConfig k M → ℝ) : Prop :=
  ∀ C, S C ≠ 0 → ConfigBalanced T e x C.1

/-- The balance gap (57), p. 37:
`G(S, x) = ∑_p W(p) ∑_C μ_S(C) min(|n_p(C) − ⌊x_p⌋|, |n_p(C) − ⌈x_p⌉|)`, the outer sum over the
non-root nodes `p` (those that have an edge to a parent of length `W(p)`; at the root
`n_root(C) = k = x_root` for consistent states, so the root term would vanish). -/
noncomputable def balanceGap (T : WTree V) {k : ℕ} {M : Type} [Fintype M] [DecidableEq M]
    (e : M ≃ T.Leaf) (S : KConfig k M → ℝ) (x : M → ℝ) : ℝ :=
  ∑ p ∈ univ.filter (fun p => p ≠ T.root), T.W p *
    ∑ C, S C * min (|(countBelow T e C.1 p : ℝ) - ⌊massBelow T e x p⌋|)
      (|(countBelow T e C.1 p : ℝ) - ⌈massBelow T e x p⌉|)

/-- The cost of moving the servers from the configuration `C` to the configuration `C'`: the
minimum, over all bijections between the two `k`-subsets (given by labellings `a`, `b` of their
points), of the total distance `∑_i dist (a i) (b i)`. -/
noncomputable def matchCost {k : ℕ} {M : Type} [MetricSpace M] (C C' : KConfig k M) : ℝ := by
  classical
  exact sInf {c : ℝ | ∃ a b : Fin k → M, Function.Injective a ∧ Function.Injective b ∧
    Finset.univ.image a = C.1 ∧ Finset.univ.image b = C'.1 ∧ c = ∑ i, dist (a i) (b i)}

/-- A coupling of the k-server states `S` and `S'`: a non-negative mass function on pairs of
configurations with marginals `S` and `S'`. -/
def IsCoupling {k : ℕ} {M : Type} [Fintype M] [DecidableEq M] (S S' : KConfig k M → ℝ)
    (q : KConfig k M × KConfig k M → ℝ) : Prop :=
  (∀ z, 0 ≤ q z) ∧ (∀ C, ∑ C', q (C, C') = S C) ∧ (∀ C', ∑ C, q (C, C') = S' C')

/-- The cost of changing the k-server state `S` to `S'`: the transportation (earthmover) cost,
the minimum over couplings `q` of `S` and `S'` of `∑_{C, C'} q(C, C') · matchCost C C'`. -/
noncomputable def transportCost {k : ℕ} {M : Type} [MetricSpace M] [Fintype M] [DecidableEq M]
    (S S' : KConfig k M → ℝ) : ℝ :=
  sInf {c : ℝ | ∃ q, IsCoupling S S' q ∧ c = ∑ z, q z * matchCost z.1 z.2}

end PolylogKServer.Rounding


