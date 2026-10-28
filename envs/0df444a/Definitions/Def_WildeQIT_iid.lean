-- Prove2me | Definitions.Def_WildeQIT_iid
-- name    : WildeQIT_iid
-- status  : Definition
-- author  : @nonlocally
-- created : 2026-09-07T07:28:43.309578+00:00
-- url     : https://prove2.me/theorems/fbaf49f3-61d1-4a0b-91ec-58b78ebe8cfe
-- title:
--   i.i.d. product distribution $p_{X^n}$ on sequences, set probabilities, letter counts (Ch. 14 setting)
-- statement:
--   Throughout Chapter 14 an information source emits $n$ independent, identically distributed copies of a random variable $X$ with distribution $p_X$ on a finite alphabet $\mathcal{X}$; a realization is a sequence $x^n = x_1\cdots x_n$ (Lean: `Fin n → α`), with $p_{X^n}(x^n) = \prod_{i=1}^n p_X(x_i)$. Entropies are in bits.
--
--   **The i.i.d. product distribution.** `FinDist.iid p n` is the distribution on sequences of length $n$ with $p_{X^n}(x^n)=\prod_{i} p_X(x_i)$ (Definition 14.2.1); it is a probability distribution because $\sum_{x^n}\prod_i p_X(x_i) = \bigl(\sum_x p_X(x)\bigr)^n = 1$.
--
--   **Probability of a set.** `FinDist.probOf p S` is $\Pr\{X\in S\} = \sum_{x\in S}p(x)$ for a finite set $S$ of letters (used with $p_{X^n}$ and a set of sequences, e.g. a typical set).
--
--   **Letter counts.** `seqCount x a` is $N(a|x^n)$, the number of positions $i$ with $x_i = a$ (§14.7, the method of types).
--
--   **Formalization Note.** `iid_prob` is a `rfl` lemma; `seqCount` needs decidable equality on the alphabet.
-- source:
--   Wilde, Quantum Information Theory 2nd ed. (Cambridge 2017; arXiv:1106.1445v8), Definition 14.2.1, §Weak Typicality (roster-items.csv line 25003); the i.i.d. distribution p_{X^n}(x^n) = ∏ p_X(x_i) stated there, and the counts N(x|x^n) of §14.7 (Definition 14.7.1).

import Definitions.Def_WildeQIT_FinDist
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.Pi

/-!
Wilde, *Quantum Information Theory* (2nd ed.), Chapter 14 (Classical Typicality), setting:
an information source emits `n` independent, identically distributed copies of a random
variable `X` with distribution `p_X`; a realization is a sequence `xⁿ = x₁ ⋯ xₙ` and
`p_{Xⁿ}(xⁿ) = ∏ᵢ p_X(xᵢ)` (Definition 14.2.1). Sequences of length `n` over the alphabet `α`
are functions `Fin n → α`. Also: the probability of a set of sequences, and the letter counts
`N(x|xⁿ)` used by the method of types (§14.7).
-/

namespace WildeQIT

namespace FinDist

variable {α : Type} [Fintype α]

/-- The i.i.d. product distribution `p_{Xⁿ}(xⁿ) = ∏ᵢ p_X(xᵢ)` on sequences `Fin n → α`. -/
noncomputable def iid (p : FinDist α) (n : ℕ) : FinDist (Fin n → α) where
  prob x := ∏ i, p.prob (x i)
  nonneg x := Finset.prod_nonneg fun i _ => p.nonneg (x i)
  sum_eq_one := by
    have h := Finset.prod_univ_sum (fun _ : Fin n => (Finset.univ : Finset α)) (fun _ a => p.prob a)
    simp only [Fintype.piFinset_univ, p.sum_eq_one, Finset.prod_const_one] at h
    exact h.symm

@[simp] theorem iid_prob (p : FinDist α) (n : ℕ) (x : Fin n → α) :
    (p.iid n).prob x = ∏ i, p.prob (x i) := rfl

/-- The probability `Pr{X ∈ S} = ∑_{x ∈ S} p(x)` of a set of letters. -/
noncomputable def probOf (p : FinDist α) (S : Finset α) : ℝ := ∑ x ∈ S, p.prob x

end FinDist

/-- The number `N(a|xⁿ)` of occurrences of the letter `a` in the sequence `xⁿ`. -/
def seqCount {α : Type} [DecidableEq α] {n : ℕ} (x : Fin n → α) (a : α) : ℕ :=
  (Finset.univ.filter fun i => x i = a).card

end WildeQIT


