-- Prove2me | Definitions.Def_AuctionMatroidInt_Alg3Round
-- name    : AuctionMatroidInt_Alg3Round
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:28:11.242919+00:00
-- url     : https://prove2.me/theorems/d95beef6-6f47-4d22-9c54-adc08bcc609f
-- title:
--   Algorithm 3: scanning, configurations inside a round, and one round
-- statement:
--   A **round** of Algorithm 3 starts from $(X^*,\pi^*)$ with $Y=X=X^*$ and $\pi=\pi^*$, scans every element of $E\setminus X^*$ exactly once, **in an arbitrary order**, applying one iteration of the inner loop to each, and ends in a state $(Y',X',\pi')$.
--
--   This module defines: the result of scanning a list of elements (one iteration per element, in order); a **configuration inside a round**, reached after scanning a list of distinct elements of $E\setminus X^*$ (these are the configurations "before and after each iteration of the inner for-loop"); and a **round**, the result of scanning some list that enumerates $E\setminus X^*$ without repetition.
--
--   **Formalization Note** `Alg3Scan` is an inductive relation over the list; `Alg3Partial` and `Alg3Round` quantify over the order, so every statement about rounds holds for every scan order and tie-break.
-- source:
--   Huang, Kobayashi, Terao, Auction-Based Algorithms for Weighted Matroid Intersection with Near-Linear Query Complexity (manuscript, sha256 2e12cb4a…), Algorithm 3, Lines 3–15, p.22, and §5.1.2, p.21 (PDF pp.23–24)

import Mathlib
import Definitions.Def_AuctionMatroidInt_Alg3Step

namespace AuctionMatroidInt

/-- **Scanning a list of elements** in the inner for-loop of Algorithm 3 (Lines 5–14, p.22):
`Alg3Scan … Xs πs l s s'` says that starting from state `s` and scanning the elements of `l` in
order, one `Alg3Step` per element, the loop can end in state `s'`. `(Xs, πs)` are the frozen
`(X*, π*)` of the round. -/
inductive Alg3Scan {α : Type*} [Fintype α] [DecidableEq α] (ε : ℝ) (w : α → ℝ)
    (I₁ I₂ : Finset α → Prop) (Xs : Finset α) (πs : α → ℝ) :
    List α → Alg3State α → Alg3State α → Prop
  | nil (s : Alg3State α) : Alg3Scan ε w I₁ I₂ Xs πs [] s s
  | cons (e : α) (l : List α) (s s' s'' : Alg3State α) :
      Alg3Step ε w I₁ I₂ Xs πs e s s' → Alg3Scan ε w I₁ I₂ Xs πs l s' s'' →
      Alg3Scan ε w I₁ I₂ Xs πs (e :: l) s s''

/-- **A configuration inside a round of Algorithm 3.** Starting the round from `(X*, π*) =
(Xs, πs)` with `Y = X = X*` (Line 3), the elements of the list `l` (distinct, none in `X*`) have
been scanned in this order, and the current state is `s`. These are the configurations "before
and after each iteration of the inner for-loop" (Lemma 5.4, p.23). -/
def Alg3Partial {α : Type*} [Fintype α] [DecidableEq α] (ε : ℝ) (w : α → ℝ)
    (I₁ I₂ : Finset α → Prop) (Xs : Finset α) (πs : α → ℝ) (l : List α) (s : Alg3State α) :
    Prop :=
  l.Nodup ∧ (∀ e ∈ l, e ∉ Xs) ∧ Alg3Scan ε w I₁ I₂ Xs πs l ⟨Xs, Xs, πs⟩ s

/-- **One round of Algorithm 3** (one iteration of the outer for-loop, Lines 3–15, p.22) from
`(X, π) = (Xs, πs)`: some list enumerating `E \ X*` without repetition, in **any** order ("the
algorithm scans each e ∈ E \ X* once, in an arbitrary order", p.21), is scanned, and the round
ends in state `s'` (whose `Y`, `X`, `π` are the `Y'`, `X'`, `π'` at the end of the round). -/
def Alg3Round {α : Type*} [Fintype α] [DecidableEq α] (ε : ℝ) (w : α → ℝ)
    (I₁ I₂ : Finset α → Prop) (Xs : Finset α) (πs : α → ℝ) (s' : Alg3State α) : Prop :=
  ∃ l : List α, l.Nodup ∧ (∀ e, e ∈ l ↔ e ∉ Xs) ∧
    Alg3Scan ε w I₁ I₂ Xs πs l ⟨Xs, Xs, πs⟩ s'

end AuctionMatroidInt


