-- Prove2me | Definitions.Def_OnlineCRS_Combine_Combination
-- name    : OnlineCRS_Combine_Combination
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T20:19:35.982859+00:00
-- url     : https://prove2.me/theorems/528ea92e-f96b-40e1-9a5f-85d715211c5c
-- title:
--   Definition 2.10, p. 15 — intersection of independently drawn greedy families
-- statement:
--   Let $\mathcal G_1$ and $\mathcal G_2$ be the families drawn by two randomized greedy online contention resolution schemes at the same input $x$. Their combination draws them independently and uses
--
--   $$
--   \mathcal G=\mathcal G_1\cap\mathcal G_2.
--   $$
--
--   The probability assigned to a resulting family is the sum of $w_1(x,\mathcal G_1)w_2(x,\mathcal G_2)$ over all pairs with this intersection. The auxiliary indicator $\chi_e(A,F,F')$ records whether $I\cup\{e\}\in F$ for every $I\subseteq A$ lying in $F'$, and its probability is calculated over $R(x)$.
--
--   These definitions name the construction and the event used in the proof of Lemma 2.11.
--
--   **Formalization Note** The product of the two family weights makes their independent randomization explicit; the paper leaves this sampling convention implicit.
-- source:
--   arXiv:1508.00142v2, Definition 2.10 and proof of Lemma 2.11, p. 15

import Mathlib
import Definitions.Def_OnlineCRS_Matroid_Basics

namespace OnlineCRS.Combine

/-- The event indicated by χₑ(A,F,F′) in the proof of Lemma 2.11, p. 15. -/
def chi {α : Type} [DecidableEq α] (e : α) (A : Finset α)
    (F F' : Finset (Finset α)) : Prop :=
  ∀ I : Finset α, I ⊆ A → I ∈ F' → insert e I ∈ F

open Classical in
/-- The probability of χₑ(R(x),F,F′) under the independent activation model. -/
noncomputable def chiProb {α : Type} [Fintype α] [DecidableEq α] (x : α → ℝ)
    (e : α) (F F' : Finset (Finset α)) : ℝ :=
  ∑ A : Finset α, if chi e A F F' then OnlineCRS.Matroid.activeProb x A else 0

/-- Definition 2.10, p. 15: intersect independently drawn greedy families. -/
noncomputable def combine {α : Type} [Fintype α] [DecidableEq α]
    (w₁ w₂ : (α → ℝ) → Finset (Finset α) → ℝ)
    (x : α → ℝ) (Fam : Finset (Finset α)) : ℝ :=
  ∑ F₁ : Finset (Finset α), ∑ F₂ : Finset (Finset α),
    w₁ x F₁ * w₂ x F₂ * (if F₁ ∩ F₂ = Fam then 1 else 0)

end OnlineCRS.Combine


