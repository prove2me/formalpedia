-- Prove2me | Definitions.Def_DynSort_OnlineAlg
-- name    : DynSort_OnlineAlg
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T21:33:47.956008+00:00
-- url     : https://prove2.me/theorems/d5c04880-a91d-4aeb-8b28-fbe216997fc8
-- title:
--   Fully dynamic sorting on $n$ cells: updates, legal arrangements, online algorithms, recourse
-- statement:
--   This module defines the problem of Theorem 1. An array has $n$ cells and stores real-valued elements that arrive online; at most $n$ elements are present at any time.
--
--   1. **Updates.** An update is either the insertion of a real $x$ or the deletion of a previously inserted element. The element inserted by the update with index $t$ (counting from $0$) is named $t$; equal values are distinct elements. The **alive** elements after a sequence $\sigma$ of updates are those inserted and not yet deleted.
--   2. **Valid sequences.** $\sigma$ is valid for $n$ cells when every deletion names an element alive just before it, and at most $n$ elements are alive after every prefix of $\sigma$.
--   3. **Arrangements.** An arrangement assigns to each of the $n$ cells an element or nothing. It is **legal** after $\sigma$ when no element occupies two cells and the stored elements are exactly the alive ones. The stored sequence $S$ lists the values of the occupied cells from left to right.
--   4. **Online algorithms.** A deterministic online algorithm on $n$ cells maps every update history to the arrangement it maintains after that history; it therefore cannot depend on future updates.
--   5. **Recourse.** The recourse of an update is the number of elements stored both before and after it that occupy different cells. The total recourse of an algorithm over $\sigma$ is the sum over its updates; amortized recourse is the total divided by the number of updates.
--
--   **Formalization Note** No computation model is imposed: the paper bounds competitive ratio and recourse, not running time. Recourse is the net change of position across one update, so an element moved away and back within an update does not count, and neither the deleted nor the inserted element counts.
-- source:
--   Azar, Bhore, Dey, Panigrahi, Vardi, Zhang, Online and Fully-Dynamic Sorting, STOC 2027 submission (manuscript sha256 da7f0d5ef6191ccaa6c70faec62234592c6d108cd2357bda3e5b6dac010acf6c), §2, pp.5–6 (PDF pp.7–8); Theorem 1, p.1 (PDF p.3)

import Mathlib
import Definitions.Def_DynSort_cost

namespace DynSort

/-! # The fully dynamic sorting problem on `n` cells

Y. Azar, S. Bhore, D. Dey, D. Panigrahi, O. Vardi, I. Zhang, *Online and Fully-Dynamic Sorting*,
STOC 2027 submission (manuscript sha256 da7f0d5e…), §2, pp.5–6 (PDF pp.7–8); Theorem 1, p.1.

An array of `n` cells stores real-valued elements that arrive online; at most `n` elements are
present at any time. An insertion assigns the new element to an empty cell, possibly rearranging
the stored elements; a deletion frees the cell of the removed element, and the algorithm may
rearrange the remaining ones. The recourse of an update is the number of previously stored
elements that change positions during that update.

**Formalization Note.**
* An update is `insert x` (`x : ℝ` arbitrary) or `delete i`. The element inserted by the update of
  index `t` (0-based) of the sequence is named `t`; equal values are distinct elements.
* `Valid n σ`: every `delete i` names an element alive just before it, and after every prefix at
  most `n` elements are alive.
* An arrangement is `Fin n → Option ℕ` (cell ↦ element). `Legal n σ a`: no element occupies two
  cells, and the occupied elements are exactly the alive ones.
* An online deterministic algorithm on `n` cells is a function from the update history to the
  arrangement after it: it cannot see later updates. No computation model is imposed (the paper
  claims no running time).
* `recourse a b` counts the elements stored both before (`a`) and after (`b`) an update at
  different cells: the net position change of that update. The deleted element and the new
  element do not count.
-/

/-- An update of the fully dynamic sorting problem (§2, p.6). -/
inductive Update where
  | insert (x : ℝ)
  | delete (i : ℕ)

/-- The elements alive after the update sequence `σ`: the update of index `t` that is
`insert x` creates element `t`, and `delete i` removes element `i`. -/
def alive (σ : List Update) : Finset ℕ :=
  σ.zipIdx.foldl
    (fun s p => match p.1 with
      | .insert _ => insert p.2 s
      | .delete i => s.erase i) ∅

/-- The value of element `i`: the real inserted by the update of index `i`. -/
noncomputable def value (σ : List Update) (i : ℕ) : ℝ :=
  match σ[i]? with
  | some (.insert x) => x
  | _ => 0

/-- **Valid update sequences on `n` cells** (§2, p.6): each deletion names a previously inserted
element that is still present, and at most `n` elements are present after every update. -/
def Valid (n : ℕ) (σ : List Update) : Prop :=
  ∀ t < σ.length,
    (∀ i, σ[t]? = some (.delete i) → i ∈ alive (σ.take t)) ∧
    (alive (σ.take (t + 1))).card ≤ n

/-- An arrangement of `n` cells: the element stored in each cell, `none` for an empty cell. -/
abbrev Arrangement (n : ℕ) := Fin n → Option ℕ

/-- **Legal arrangement** after `σ`: each element occupies at most one cell, and the stored
elements are exactly the alive elements. -/
def Legal (n : ℕ) (σ : List Update) (a : Arrangement n) : Prop :=
  (∀ c c' : Fin n, ∀ i, a c = some i → a c' = some i → c = c') ∧
  ∀ i, (∃ c, a c = some i) ↔ i ∈ alive σ

/-- **A deterministic online algorithm on `n` cells** (Theorem 1, p.1; §2, p.6): the arrangement
it maintains after each update history. Being a function of the history, it is online. -/
abbrev OnlineAlg (n : ℕ) := List Update → Arrangement n

/-- The stored sequence `S`: the values of the occupied cells, left to right, ignoring empty
cells (§2, p.6). -/
noncomputable def seq {n : ℕ} (σ : List Update) (a : Arrangement n) : List ℝ :=
  (List.finRange n).filterMap (fun c => (a c).map (value σ))

open Classical in
/-- **Recourse of an update** (§2, p.6): the number of elements stored before (`a`) and after
(`b`) the update that occupy different cells. -/
noncomputable def recourse {n : ℕ} (a b : Arrangement n) : ℕ :=
  (Finset.univ.filter (fun c : Fin n =>
    ∃ i, a c = some i ∧ (∃ c', b c' = some i) ∧ b c ≠ some i)).card

/-- **Total recourse** of an online algorithm over the update sequence `σ`: the sum over its
updates of the recourse between the arrangements before and after the update. Amortized recourse
is this total divided by `σ.length` (§2, p.6). -/
noncomputable def totalRecourse {n : ℕ} (alg : OnlineAlg n) (σ : List Update) : ℕ :=
  ∑ t ∈ Finset.range σ.length, recourse (alg (σ.take t)) (alg (σ.take (t + 1)))

end DynSort


