-- Prove2me | Definitions.Def_RankingCertGap_OrderState
-- name    : RankingCertGap_OrderState
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:47:59.650227+00:00
-- url     : https://prove2.me/theorems/44ee87f2-d2b5-4f55-9d91-9f38e7fd6826
-- title:
--   Order events and rooted order states
-- statement:
--   For a finite set $W$ of offline vertices and a strict partial order $\prec$ on $W$, the **order event** is
--
--   $$
--   O(W,\prec):=\{Y_{i_1}<Y_{i_2}\text{ whenever }i_1,i_2\in W\text{ and }i_1\prec i_2\}.
--   $$
--
--   A **rooted order state** for $i$ is a triple $(W,\prec;i)$ such that $i\in W$ is the unique maximal element of the finite poset $(W,\prec)$. The set $W$ is its witness set. On online-degree-two instances, safety events of offline vertices take this form.
--
--   **Formalization Note** The relation is a Lean relation on all offline vertices, of which only the part on $W$ is read; being a strict partial order is stated on $W$. "Unique maximal" is stated literally: $i$ is maximal and every maximal element equals $i$.
-- source:
--   Xu, Certifying Capacity and Gaps of the Rank-Dependent Gain-Sharing Framework for Ranking, arXiv:2610.17545 (held file sha256 75896dd9…), eq. (36), p.17

import Mathlib

namespace RankingCertGap

variable {m : ℕ}

/-- The order event `O(W, ≺) := {Y_{i₁} < Y_{i₂} whenever i₁, i₂ ∈ W and i₁ ≺ i₂}`. Xu,
arXiv:2610.17545 (held file sha256 75896dd9…), eq. (36), p.17. -/
def orderEvent (W : Finset (Fin m)) (r : Fin m → Fin m → Prop) (Y : Fin m → ℝ) : Prop :=
  ∀ a ∈ W, ∀ b ∈ W, r a b → Y a < Y b

/-- A rooted order state for `i`: "a triple `(W, ≺; i)` such that `i ∈ W` is the unique maximal
element of the finite poset `(W, ≺)`" (p.17).

**Formalization Note.** `r` is a strict partial order on `W`: irreflexive and transitive on `W`.
Its values off `W` are not read. -/
def IsRootedOrderState (W : Finset (Fin m)) (r : Fin m → Fin m → Prop) (i : Fin m) : Prop :=
  i ∈ W ∧
    (∀ a ∈ W, ¬ r a a) ∧
    (∀ a ∈ W, ∀ b ∈ W, ∀ c ∈ W, r a b → r b c → r a c) ∧
    (∀ b ∈ W, ¬ r i b) ∧
    (∀ a ∈ W, (∀ b ∈ W, ¬ r a b) → a = i)

end RankingCertGap


