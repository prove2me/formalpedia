-- Prove2me | Definitions.Def_AlmostMMS_SimulSatisfied
-- name    : AlmostMMS_SimulSatisfied
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T10:47:41.00551+00:00
-- url     : https://prove2.me/theorems/a35d1065-2650-472e-bfce-f1fac9151d2b
-- title:
--   Definition 2.2, p.12 — simultaneous satisfaction by distinct items
-- statement:
--   A set $B$ of items **satisfies** a demand profile $\pi$ for agent $i$ if each demand $\alpha\in\pi$ can be assigned a distinct item $e\in B$ with $v_i(e)\ge\alpha$. The profiles $\pi_i$, $i\in I$, are **simultaneously satisfied** using distinct items of $F$ if pairwise disjoint subsets $B_i\subseteq F$ satisfy them. The module also names the first $K$ items of $F$ in the item order.
--
--   **Formalization Note** The type `π.ToType` has one element per occurrence of a demand, so equal demands need distinct items.
-- source:
--   Feige, Grinberg, Almost-MMS allocations with small agent redundancy, STOC 2027 submission, arXiv:2611.05360 (manuscript sha256 3925c4ab…), Definition 2.2, p.12; Lemma 2.2, p.12

import Mathlib

namespace AlmostMMS

open Finset

open Classical in
/-- **Satisfying a demand profile** (Definition 2.2, p.12): the set `B` of items satisfies `π` for agent
`i` if each demand of `π` can be assigned a distinct item `e ∈ B` with `v_i(e) ≥ α`.
Feige, Grinberg, STOC 2027 submission, arXiv:2611.05360 (manuscript sha256 3925c4ab…).

**Formalization Note.** `π.ToType` has one element per demand occurrence, so equal demands of a multiset
need distinct items. -/
def SatisfiesProfile {n m : ℕ} (v : Fin n → Fin m → ℝ) (i : Fin n) (B : Finset (Fin m))
    (π : Multiset ℝ) : Prop :=
  ∃ f : π.ToType → Fin m, Function.Injective f ∧ ∀ x, f x ∈ B ∧ x.1 ≤ v i (f x)

/-- **Simultaneous satisfaction** (Lemma 2.2, p.12): all profiles `π i`, `i ∈ I`, are satisfied using
distinct items of `F`. -/
def SimulSatisfied {n m : ℕ} (v : Fin n → Fin m → ℝ) (I : Finset (Fin n)) (π : Fin n → Multiset ℝ)
    (F : Finset (Fin m)) : Prop :=
  ∃ B : Fin n → Finset (Fin m), (∀ i ∈ I, B i ⊆ F) ∧ (I : Set (Fin n)).PairwiseDisjoint B ∧
    ∀ i ∈ I, SatisfiesProfile v i (B i) (π i)

/-- The first `K` items of `F` in the item order (Lemma 2.2, p.12). -/
def firstItems {m : ℕ} (F : Finset (Fin m)) (K : ℕ) : Finset (Fin m) :=
  F.filter fun e => (F.filter fun e' => e' ≤ e).card ≤ K

end AlmostMMS


