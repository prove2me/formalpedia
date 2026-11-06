-- Prove2me | Definitions.Def_HMBinPacking_Oracles
-- name    : HMBinPacking_Oracles
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T00:00:59.764259+00:00
-- url     : https://prove2.me/theorems/d93f6f8e-1177-4e7f-a692-949f793630e7
-- title:
--   Strong separation and strong optimization answers
-- statement:
--   Let $Q\subseteq\mathbb R^n$.
--
--   1. A **strong separation answer** for a query $y\in\mathbb Q^n$ either certifies $y\in Q$, or returns $u\in\mathbb Q^n$ and $\alpha\in\mathbb Q$ such that
--   $$
--   u^\top x\le\alpha<u^\top y\qquad\text{for every } x\in Q .
--   $$
--   2. A **strong optimization answer** for an objective $u\in\mathbb Q^n$ (over a nonempty polytope $Q$) is a rational point $x\in Q$ maximizing $u^\top x$ over $Q$.
--
--   Lemma 5 uses separation oracles over closed convex sets, Lemma 6 turns optimization into separation, and Lemmas 7 and 8 implement separation over $P_r$ and $K$.
--
--   **Formalization Note** Answers are binary words. A separation answer is $[\mathsf{true}]$ (certifying $y\in Q$) or $\mathsf{false}$ followed by the codes of $u$ and $\alpha$; the two cases exclude each other. An optimization answer is the code of the point. The encoding length of an answer is the length of its word.
-- source:
--   Koana, Kumabe, High-Multiplicity Bin Packing is FPT, arXiv:2609.16923v2, §3, p.5 (strong separation oracle, strong optimization oracle)

import Mathlib
import Definitions.Def_ExponomialAssortment_FPTAS_Machine
import Definitions.Def_HMBinPacking_Encoding
import Definitions.Def_HMBinPacking_Casts
open ExponomialAssortment.FPTAS (encodeRat)

namespace HMBinPacking

/-- **A correct answer of a strong separation oracle.**
Koana, Kumabe, arXiv:2609.16923v2, §3, p.5: "A strong separation oracle for a closed convex set
Q ⊆ R^n, on input y ∈ Q^n, either certifies y ∈ Q or returns u ∈ Q^n and α ∈ Q such that
u⊤x ≤ α < u⊤y for every x ∈ Q."

`IsSepAnswer Q y w` holds when either `w = [true]` and `y ∈ Q`, or `w` is `false` followed by the
codes of `u ∈ ℚ^n` and `α ∈ ℚ` with `u⊤x ≤ α` for every `x ∈ Q` and `α < u⊤y`.

**Formalization Note.** Answers are binary words: `[true]` certifies membership; a separating
inequality is written `false :: (encVec u ++ encodeRat α)`. The two cases exclude each other. The
encoding length of the answer is the length of `w`. The strict inequality `α < u⊤y` is required also
when `Q` is empty, as in the paper's answer `0⊤x ≤ −1` for `P_r = ∅` (proof of Lemma 7, p.5). -/
def IsSepAnswer {n : ℕ} (Q : Set (Fin n → ℝ)) (y : Fin n → ℚ) (w : List Bool) : Prop :=
  (w = [true] ∧ qCast y ∈ Q) ∨
    ∃ (u : Fin n → ℚ) (α : ℚ), w = false :: (encVec u ++ encodeRat α) ∧
      (∀ x ∈ Q, ∑ i, (u i : ℝ) * x i ≤ (α : ℝ)) ∧ (α : ℝ) < ∑ i, (u i : ℝ) * (y i : ℝ)

/-- **A correct answer of a strong optimization oracle.**
Koana, Kumabe, arXiv:2609.16923v2, §3, p.5: "A strong optimization oracle for a nonempty rational
polytope Q ⊆ R^n, on input u ∈ Q^n, returns a rational point of Q maximizing u⊤x."

**Formalization Note.** The answer is the code `encVec x` of a rational point `x ∈ Q` with
`u⊤x' ≤ u⊤x` for every `x' ∈ Q`. -/
def IsOptAnswer {n : ℕ} (Q : Set (Fin n → ℝ)) (u : Fin n → ℚ) (w : List Bool) : Prop :=
  ∃ x : Fin n → ℚ, w = encVec x ∧ qCast x ∈ Q ∧
    ∀ x' ∈ Q, ∑ i, (u i : ℝ) * x' i ≤ ∑ i, (u i : ℝ) * (x i : ℝ)

end HMBinPacking


