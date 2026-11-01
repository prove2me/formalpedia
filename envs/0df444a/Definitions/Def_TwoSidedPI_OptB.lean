-- Prove2me | Definitions.Def_TwoSidedPI_OptB
-- name    : TwoSidedPI_OptB
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:11:45.870775+00:00
-- url     : https://prove2.me/theorems/6671faf6-b468-435c-b8d4-fea374406cb1
-- title:
--   Feasible additions, $v(\mathrm{OPT}_B(v\mid A_B,r))$, the welfare benchmark and the pointwise buyer threshold
-- statement:
--   Let $B$ be a finite set of buyers carrying a matroid $\mathcal M_B=(B,\mathcal I_B)$, and $S$ a finite set of unit-supply sellers. A buyer $i$ **can be feasibly added** to a set $A_B\subseteq B$ of served buyers with $r$ items left for buyers when $A_B\cup\{i\}\in\mathcal I_B$ and $|A_B\cup\{i\}|\le r$.
--
--   For buyer values $v=(v_i)_{i\in B}$, the value of the restricted buyers-only optimum is
--   $$
--   v\big(\mathrm{OPT}_B(v\mid A_B,r)\big)=\max\Big\{\sum_{i\in B'}v_i \;:\; B'\subseteq B\setminus A_B,\ B'\cup A_B\in\mathcal I_B,\ |B'\cup A_B|\le r\Big\},
--   $$
--   the largest welfare increase from giving items to buyers only when $A_B$ is already served and at most $r$ items go to buyers in total. The **benchmark** is the optimal social welfare
--   $$
--   \max_{X^*}v(X^*)=\max\Big\{\sum_{i\in B'}v_i+\sum_{j\in K}v_j \;:\; B'\in\mathcal I_B,\ K\subseteq S,\ |B'|+|K|\le|S|\Big\},
--   $$
--   where $B'$ are the buyers served and $K$ the sellers keeping their own item. The **pointwise threshold** of buyer $i$ is
--   $$
--   p_i(A_B,r,v)=v\big(\mathrm{OPT}_B(v\mid A_B,r)\big)-v\big(\mathrm{OPT}_B(v\mid A_B\cup\{i\},r)\big)
--   $$
--   if $i$ can be feasibly added, and $p_i(A_B,r,v)=\infty$ otherwise.
--
--   These objects define the prices of Mechanism 1 and the benchmark of its approximation guarantee.
--
--   **Formalization Note** The matroid is a Mathlib `Matroid B` (the theorems assume `M.E = univ`). `optB` is a maximum over a finite family, which is nonempty exactly when $A_B\in\mathcal I_B$ and $|A_B|\le r$; outside that case it is set to $0$, and no statement of the mission evaluates it there. In `opt` a profile is a function on `B ⊕ S`. $\infty$ is `⊤ : WithTop ℝ`.
-- source:
--   Braun, Kesselheim, Truthful Mechanisms for Two-Sided Markets via Prophet Inequalities, arXiv:2105.15032v1, §2, p.7 (welfare, max over allocations); §3, p.9 (OPT_B(v|A_B, r)); p.10 (p_i(A_B, r, v))

import Mathlib

namespace TwoSidedPI

/-- The condition `A_B ∪ {i} ∈ ℐ_B` and `|A_B ∪ {i}| ≤ r` under which buyer `i` can still be
feasibly added (Braun, Kesselheim, arXiv:2105.15032v1, §3, p.10).

**Formalization Note** The matroid `M_B = (B, ℐ_B)` is a Mathlib `Matroid B`; the theorems of
this mission assume `M.E = Set.univ`, so that `ℐ_B` is a family of subsets of all of `B`. As
printed, the condition does not require `i ∉ A_B`. -/
def CanAdd {B : Type*} [DecidableEq B] (M : Matroid B) (AB : Finset B) (r : ℕ) (i : B) : Prop :=
  M.Indep ↑(insert i AB) ∧ (insert i AB).card ≤ r

/-- The value `v(OPT_B(v | A_B, r))` (Braun, Kesselheim, arXiv:2105.15032v1, §3, p.9):
the maximum of `∑_{i ∈ B'} v_i` over the sets `B' ⊆ B \ A_B` with `B' ∪ A_B ∈ ℐ_B` and
`|B' ∪ A_B| ≤ r`, i.e. the largest welfare increase obtainable by giving items to buyers only,
when the buyers `A_B` already hold items and at most `r` items go to buyers in total.

**Formalization Note** The maximum is a `Finset.sup'` over the (finite) feasible family. The
family is nonempty exactly when `M.Indep ↑A_B` and `|A_B| ≤ r` (it then contains `B' = ∅`);
outside that case the value is set to `0`. Every statement of this mission evaluates `optB`
only inside that case. -/
noncomputable def optB {B : Type*} [Fintype B] [DecidableEq B] (M : Matroid B) (v : B → ℝ)
    (AB : Finset B) (r : ℕ) : ℝ := by
  classical
  exact
    let F := Finset.univ.filter
      (fun B' : Finset B => Disjoint B' AB ∧ M.Indep ↑(B' ∪ AB) ∧ (B' ∪ AB).card ≤ r)
    if h : F.Nonempty then F.sup' h (fun B' => ∑ i ∈ B', v i) else 0

/-- The benchmark `max_{X*} v(X*)` of a matroid double auction with unit-demand buyers `B` and
unit-supply sellers `S` (Braun, Kesselheim, arXiv:2105.15032v1, §2, p.7 and §3, p.8): the
maximum of `∑_{i ∈ B'} v_i + ∑_{j ∈ K} v_j` over `B' ∈ ℐ_B` (the buyers who receive an item)
and `K ⊆ S` (the sellers who keep their own item) with `|B'| + |K| ≤ |S|`.

**Formalization Note** A feasible allocation gives each of the `|S|` identical items to at most
one agent, a seller only her own item, and the set of buyers served must be independent in
`M_B`; a unit-demand buyer gains nothing from a second item. The pairs `(B', K)` above are
exactly the agent sets served by such allocations, so this is the paper's maximum, not a
relaxation. Values are a profile `v : B ⊕ S → ℝ` (agents are `B ⊕ S`, so `B ∩ S = ∅`). -/
noncomputable def opt {B S : Type*} [Fintype B] [DecidableEq B] [Fintype S] [DecidableEq S]
    (M : Matroid B) (v : B ⊕ S → ℝ) : ℝ := by
  classical
  exact
    let F := Finset.univ.filter
      (fun X : Finset B × Finset S => M.Indep ↑X.1 ∧ X.1.card + X.2.card ≤ Fintype.card S)
    if h : F.Nonempty then
      F.sup' h (fun X => ∑ i ∈ X.1, v (Sum.inl i) + ∑ j ∈ X.2, v (Sum.inr j))
    else 0

/-- The pointwise buyer threshold `p_i(A_B, r, v)` (Braun, Kesselheim, arXiv:2105.15032v1, §3,
p.10): `v(OPT_B(v | A_B, r)) − v(OPT_B(v | A_B ∪ {i}, r))` if `A_B ∪ {i} ∈ ℐ_B` and
`|A_B ∪ {i}| ≤ r`, and `∞` otherwise.

**Formalization Note** `∞` is `⊤ : WithTop ℝ`; a finite value is the coercion of the real
difference. -/
noncomputable def thrPt {B : Type*} [Fintype B] [DecidableEq B] (M : Matroid B) (v : B → ℝ)
    (AB : Finset B) (r : ℕ) (i : B) : WithTop ℝ := by
  classical
  exact if CanAdd M AB r i then ((optB M v AB r - optB M v (insert i AB) r : ℝ) : WithTop ℝ)
    else ⊤

end TwoSidedPI


