-- Prove2me | Definitions.Def_ForestRoundingNSW_Rounding_ForestCoupling
-- name    : ForestRoundingNSW_Rounding_ForestCoupling
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-11T02:51:18.620333+00:00
-- url     : https://prove2.me/theorems/3ff5f173-c11b-4981-9771-25f1c7f2f906
-- title:
--   Algorithm 2 (coupling balanced distributions on a forest): rootings and the joint law of the bundles (§3.3)
-- statement:
--   Let $y\in P$ have a support graph that is a forest, and let $f_i$ be a set function per agent with a choice rule $\rho_i$. **Algorithm 2** roots each component of the support graph that contains an edge at an item; each root item $j$ gets owner $i$ with probability $y_{ij}$, or no owner with the remaining probability. Then the non-isolated agents are processed in nondecreasing order of depth: agent $i$ with parent item $p$ runs Algorithm 1 for $f_i$ from $y_i$ with transitions conditioned on $p\in S$ if $i$ owns $p$, and on $p\notin S$ otherwise, obtaining $S_i$; every child item $j\in S_i$ goes to $i$, and every child item $j\notin S_i$ goes to child agent $h$ of $j$ with probability $y_{hj}/(1-y_{ij})$, or to no one. Isolated agents keep $S_i=\emptyset$.
--
--   A **rooting** $R$ records the parent item of each agent, the parent agent of each item and the depth of each agent. `IsRooting y R` says that the parent links are exactly the edges of the support graph, each oriented one way; that exactly the isolated agents have no parent item; and that an agent's depth is $0$ below a root item and one more than its grandparent agent's depth otherwise. Such a rooting exists exactly when the support graph is a forest, and then each component with an edge has one root, an item. `alg2Law f ρ y R` is the joint law of $(S_i)_i$.
--
--   **Formalization Note.** Agents of equal depth are processed in index order. Categorical choices are sampled by sequential coins $w/(\text{remaining mass})$, which gives each option exactly its weight when the weights are nonnegative with sum at most $1$.
-- source:
--   Feng, Hu, Li, Zhang, Correlated Forest Rounding for Unweighted Nash Social Welfare, STOC 2027 submission (manuscript sha256 0c7af642…), p. 22, Lemma 3.3 and Figure 1; p. 23, Algorithm 2

import Mathlib
import Definitions.Def_ForestRoundingNSW_Rounding_BalancedRounding

/-!
# Algorithm 2 (coupling balanced distributions on a forest): its joint law

Feng, Hu, Li, Zhang, *Correlated Forest Rounding for Unweighted Nash Social Welfare*, STOC 2027
submission (manuscript sha256 0c7af642…): Algorithm 2 (p. 23), Lemma 3.3 (p. 22), Figure 1.

Algorithm 2 on a fractional allocation `y` (agents `Fin n`, items `Fin m`) with forest support:
every component of the support graph that contains an edge is rooted at an item; each root item
`j` gets owner `i` with probability `y_ij`, or no owner with the remaining probability; then the
non-isolated agents are processed in nondecreasing order of depth: agent `i` with parent item `p`
runs Algorithm 1 for `f_i` from `y_i` with the transitions conditioned on `p ∈ S` if `i` owns `p`
and on `p ∉ S` otherwise, obtaining `S_i`; every child item `j ∈ S_i` goes to `i`; every child item
`j ∉ S_i` goes to child agent `h` of `j` with probability `y_hj / (1 − y_ij)`, or to no one.
Isolated agents keep `S_i = ∅`.

Encoding.
* A rooting is given as data (`Rooting`): the parent item of each agent (`none` for an isolated
  agent), the parent agent of each item (`none` for a root item or an isolated item), and the
  depth of each agent. `IsRooting y R` says that the parent links are exactly the edges of the
  support graph, each edge oriented one way, that exactly the isolated agents have no parent, and
  that an agent's depth is `0` below a root item and one more than its grandparent agent's depth
  otherwise. Such a rooting exists iff the support graph is a forest, and then every component
  with an edge has exactly one root, which is an item. The paper leaves the choice of roots open.
* Agents are processed in the order `agentOrder R`: by depth, ties by index (agents of equal
  depth touch disjoint items).
* `categorical l 1` draws `some a` with probability `w` for each `(a, w)` in the list `l` and
  `none` with the remaining probability, by sequential coins `w / (remaining mass)`.
* Each agent `i` uses its own choice rule `ρ i` for Algorithm 1.
* The algorithm's state is the owner of every item and the bundle of every agent; `alg2Law` is the
  joint law of the bundles `(S_i)_i`.
-/

namespace ForestRoundingNSW.Rounding

variable {n m : ℕ}

/-- A rooting of the support forest: parent item of each agent, parent agent of each item, and
the depth of each agent. -/
structure Rooting (n m : ℕ) where
  /-- The parent item of an agent (`none`: isolated agent). -/
  agentParent : Fin n → Option (Fin m)
  /-- The parent agent of an item (`none`: a root item or an isolated item). -/
  itemParent : Fin m → Option (Fin n)
  /-- The depth of an agent (number of agents strictly above it). -/
  depth : Fin n → ℕ

/-- `R` roots every component of the support graph of `y` that has an edge at an item. -/
def IsRooting (y : Fin n → Fin m → ℝ) (R : Rooting n m) : Prop :=
  (∀ i j, 0 < y i j ↔ (R.agentParent i = some j ∨ R.itemParent j = some i)) ∧
  (∀ i j, ¬ (R.agentParent i = some j ∧ R.itemParent j = some i)) ∧
  (∀ i, R.agentParent i = none ↔ ∀ j, y i j = 0) ∧
  (∀ i j, R.agentParent i = some j → R.itemParent j = none → R.depth i = 0) ∧
  (∀ i j i', R.agentParent i = some j → R.itemParent j = some i' → R.depth i = R.depth i' + 1)

/-- The agents in nondecreasing order of depth (ties by index). -/
def agentOrder (R : Rooting n m) : List (Fin n) :=
  (List.finRange n).mergeSort fun a b => decide (R.depth a ≤ R.depth b)

/-- Draw `some a` with probability `w` for each `(a, w)` in the list, `none` with the remaining
probability (`mass` is the probability not yet assigned; start with `1`). -/
noncomputable def categorical {α : Type} : List (α × ℝ) → ℝ → PMF (Option α)
  | [], _ => PMF.pure none
  | (a, w) :: rest, mass =>
    (coin (w / mass)).bind fun b => if b then PMF.pure (some a) else categorical rest (mass - w)

/-- A sequence of random updates of a state, one per list element. -/
noncomputable def foldPMF {σ β : Type} (g : σ → β → PMF σ) : List β → σ → PMF σ
  | [], s => PMF.pure s
  | b :: bs, s => (g s b).bind fun s' => foldPMF g bs s'

/-- The state of Algorithm 2: the owner of every item and the bundle of every agent. -/
structure CState (n m : ℕ) where
  /-- The owner of each item (`none`: no owner yet / no owner). -/
  owner : Fin m → Option (Fin n)
  /-- The bundle of each agent. -/
  bundle : Fin n → Finset (Fin m)

/-- Lines 3–4: a root item `j` gets owner `i` with probability `y_ij`, or no owner. -/
noncomputable def rootStep (y : Fin n → Fin m → ℝ) (R : Rooting n m) (s : CState n m)
    (j : Fin m) : PMF (CState n m) :=
  if R.itemParent j = none then
    (categorical ((List.finRange n).map fun i => (i, y i j)) 1).map fun o =>
      { s with owner := Function.update s.owner j o }
  else PMF.pure s

/-- Lines 8–10 for a child item `j` of agent `i` with sampled bundle `S`: `j` goes to `i` if
`j ∈ S`, and otherwise to child agent `h` of `j` with probability `y_hj / (1 − y_ij)`, or to no
one. -/
noncomputable def childStep (y : Fin n → Fin m → ℝ) (R : Rooting n m) (i : Fin n)
    (S : Finset (Fin m)) (s : CState n m) (j : Fin m) : PMF (CState n m) :=
  if R.itemParent j = some i then
    if j ∈ S then PMF.pure { s with owner := Function.update s.owner j (some i) }
    else
      (categorical (((List.finRange n).filter fun h => R.agentParent h = some j).map
          fun h => (h, y h j / (1 - y i j))) 1).map fun o =>
        { s with owner := Function.update s.owner j o }
  else PMF.pure s

/-- Lines 6–10 for agent `i`: conditioned balanced rounding given the ownership of its parent
item, then the ownership of its child items. -/
noncomputable def agentStep (f : Fin n → Finset (Fin m) → ℝ)
    (ρ : Fin n → (Fin m → ℝ) → Fin m × Fin m) (y : Fin n → Fin m → ℝ) (R : Rooting n m)
    (s : CState n m) (i : Fin n) : PMF (CState n m) :=
  match R.agentParent i with
  | none => PMF.pure s
  | some p =>
    (condLaw (f i) (ρ i) (y i) p (decide (s.owner p = some i))).bind fun S =>
      foldPMF (childStep y R i S) (List.finRange m)
        { s with bundle := Function.update s.bundle i S }

/-- The joint law of the bundles `(S_i)_i` returned by Algorithm 2 with rooting `R` and choice
rules `ρ`. -/
noncomputable def alg2Law (f : Fin n → Finset (Fin m) → ℝ)
    (ρ : Fin n → (Fin m → ℝ) → Fin m × Fin m) (y : Fin n → Fin m → ℝ) (R : Rooting n m) :
    PMF (Fin n → Finset (Fin m)) :=
  ((foldPMF (rootStep y R) (List.finRange m) ⟨fun _ => none, fun _ => ∅⟩).bind fun s =>
    foldPMF (agentStep f ρ y R) (agentOrder R) s).map CState.bundle

end ForestRoundingNSW.Rounding


