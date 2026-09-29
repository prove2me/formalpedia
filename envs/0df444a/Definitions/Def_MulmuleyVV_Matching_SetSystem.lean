-- Prove2me | Definitions.Def_MulmuleyVV_Matching_SetSystem
-- name    : MulmuleyVV_Matching_SetSystem
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T16:33:23.839534+00:00
-- url     : https://prove2.me/theorems/71f3e0d1-9979-47e8-91ac-5f72c393a0e4
-- title:
--   Set systems: the weight of a set and a unique minimum (maximum) weight set
-- statement:
--   Let $S$ be a finite set of elements and let $F$ be a family of subsets of $S$; the pair $(S, F)$ is a **set system**. Assign a weight $w_x \in \mathbb{N}$ to each element $x \in S$. The **weight** of a set $T \subseteq S$ is
--
--   $$
--   w(T) = \sum_{x \in T} w_x .
--   $$
--
--   The family $F$ **has a unique minimum weight set** under $w$ if some $S_0 \in F$ satisfies $w(S_0) < w(T)$ for every $T \in F$ with $T \neq S_0$. Symmetrically, $F$ **has a unique maximum weight set** if some $S_0 \in F$ satisfies $w(T) < w(S_0)$ for every other $T \in F$.
--
--   These are the objects of the isolating lemma (Lemma 1) and of the remark that follows it. An empty family has neither a unique minimum nor a unique maximum.
--
--   **Formalization Note** The ground set is a finite type `α`, sets are `Finset α`, the family is `F : Finset (Finset α)`, and weights are functions `α → ℕ`. `setWeight w T`, `HasUniqueMin F w` and `HasUniqueMax F w` are the three declarations.
-- source:
--   Mulmuley, Vazirani, Vazirani, Matching is as easy as matrix inversion, Combinatorica 7 (1987), p. 107, §3 (Definition of a set system and of the weight of a set; Lemma 1)

import Mathlib

namespace MulmuleyVV.Matching

/-- The weight of a set `T` of elements under the element weights `w`:
`∑_{x ∈ T} w x` (Mulmuley–Vazirani–Vazirani 1987, §3, p. 107). -/
def setWeight {α : Type*} (w : α → ℕ) (T : Finset α) : ℕ :=
  ∑ x ∈ T, w x

/-- The family `F` has a unique minimum weight set under `w`: some `S ∈ F` is strictly lighter
than every other member of `F` (MVV 1987, §3, Lemma 1, p. 107). -/
def HasUniqueMin {α : Type*} (F : Finset (Finset α)) (w : α → ℕ) : Prop :=
  ∃ S ∈ F, ∀ T ∈ F, T ≠ S → setWeight w S < setWeight w T

/-- The family `F` has a unique maximum weight set under `w`: some `S ∈ F` is strictly heavier
than every other member of `F` (MVV 1987, §3, remark after Lemma 1, p. 107). -/
def HasUniqueMax {α : Type*} (F : Finset (Finset α)) (w : α → ℕ) : Prop :=
  ∃ S ∈ F, ∀ T ∈ F, T ≠ S → setWeight w T < setWeight w S

end MulmuleyVV.Matching


