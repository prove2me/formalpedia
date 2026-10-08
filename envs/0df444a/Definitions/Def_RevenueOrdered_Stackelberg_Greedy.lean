-- Prove2me | Definitions.Def_RevenueOrdered_Stackelberg_Greedy
-- name    : RevenueOrdered_Stackelberg_Greedy
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T03:51:12.570545+00:00
-- url     : https://prove2.me/theorems/25448245-e4bb-4d2e-9198-db8d2cffa05b
-- title:
--   §4.6, p. 22 — the greedy algorithm $\mathrm{greedy}(F, L)$ run on a subset $F$ in the order induced by $L$
-- statement:
--   This module defines the greedy algorithm of §4.6 of Berbeglia and Joret.
--
--   Let $\mathcal X$ be a family of "independent" finite sets of elements, $L$ a linear ordering of the elements and $F$ a set of elements. Enumerate the elements of $F$ as $e_1,\dots,e_m$ in the order induced by $L$. The greedy algorithm sets $I_0=\emptyset$ and, for $i=1,\dots,m$,
--   $$
--   I_i=\begin{cases} I_{i-1}\cup\{e_i\} & \text{if } I_{i-1}\cup\{e_i\}\in\mathcal X,\\ I_{i-1} & \text{otherwise,}\end{cases}
--   $$
--   and outputs $\mathrm{greedy}(F,L)=I_m$. For a matroid $M$ this is $\mathrm{greedy}_M(F,L)$, computed with the independent sets of $M$.
--
--   A **linear ordering** of a finite set $E$ is an enumeration of $E$ without repetitions; $e<_L f$ means that $e$ is listed before $f$.
--
--   The greedy algorithm models the customer of the Stackelberg Matroid problem, who buys a minimum-weight base, and it also defines the choice probabilities of the assortment instance of Theorem 4.16.
--
--   **Formalization Note** An ordering is a duplicate-free `List`; `greedy` folds over the whole list and skips elements outside $F$, so $F$ is scanned in the order induced by $L$ and is not re-sorted. The independence predicate is an arbitrary predicate on finite sets, because the auxiliary system $M'$ of Theorem 4.16 is used before it is shown to be a matroid; `greedyM` specialises it to a Mathlib `Matroid`.
-- source:
--   Berbeglia & Joret, Assortment Optimisation Under a General Discrete Choice Model: A Tight Analysis of Revenue-Ordered Assortments, arXiv:1606.01371v3, p. 22, §4.6 (definition of the greedy algorithm)

import Mathlib

namespace RevenueOrdered.Stackelberg

open Classical in
/-- The greedy algorithm (Berbeglia–Joret, arXiv:1606.01371v3, §4.6, p. 22), run on the subset
`F` with the linear ordering `L` and the independence predicate `Indep`. The list `L` enumerates
the elements in order; scanning it from left to right, starting from `I₀ = ∅`, an element `e` is
added to the current set `I` when `e ∈ F` and `I ∪ {e}` is independent, and skipped otherwise.
Elements of `L` outside `F` are skipped, so `F` is scanned in the order induced by `L`, as on
p. 22. The output is the last set computed. The predicate is arbitrary (it need not come from a
matroid), so the same definition serves the auxiliary system `M′` of the proof of Theorem 4.16. -/
noncomputable def greedy {β : Type*} (Indep : Finset β → Prop) (L : List β) (F : Finset β) :
    Finset β :=
  L.foldl (fun I e => if e ∈ F ∧ Indep (insert e I) then insert e I else I) ∅

/-- `greedy_M(F, L)` for a matroid `M` (p. 23, Lemma 4.14): the greedy algorithm with the
independence predicate of `M`. -/
noncomputable def greedyM {α : Type*} (M : Matroid α) (L : List α) (F : Finset α) : Finset α :=
  greedy (fun X => M.Indep (X : Set α)) L F

/-- `L` is a linear ordering of the finite set `E`: a duplicate-free list whose elements are
exactly those of `E`. Position in the list is the order (`e <_L f` iff `e` occurs before `f`). -/
def IsLinearOrderOf {β : Type*} [DecidableEq β] (L : List β) (E : Finset β) : Prop :=
  L.Nodup ∧ L.toFinset = E

end RevenueOrdered.Stackelberg


