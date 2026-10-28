-- Prove2me | Definitions.Def_WildeQIT_typicalSet
-- name    : WildeQIT_typicalSet
-- status  : Definition
-- author  : @nonlocally
-- created : 2026-09-07T07:42:10.136719+00:00
-- url     : https://prove2.me/theorems/35a52653-f0ad-455f-9d43-e0ab08f0a577
-- title:
--   Typical sequences and the typical set $T_\delta^{X^n}$ (Definitions 14.2.2–14.2.3)
-- statement:
--   Throughout Chapter 14 an information source emits $n$ independent, identically distributed copies of a random variable $X$ with distribution $p_X$ on a finite alphabet $\mathcal{X}$; a realization is a sequence $x^n = x_1\cdots x_n$ (Lean: `Fin n → α`), with $p_{X^n}(x^n) = \prod_{i=1}^n p_X(x_i)$. Entropies are in bits.
--
--   **Definition 14.2.2 (Typical sequence).** A sequence $x^n$ is $\delta$-typical if its sample entropy $\overline{H}(x^n)$ is $\delta$-close to the entropy $H(X)$ of the random variable $X$ that is the source of the sequence.
--
--   **Definition 14.2.3 (Typical set).** The $\delta$-typical set $T_\delta^{X^n}$ is the set of all $\delta$-typical sequences:
--
--   $$
--   T_\delta^{X^n} \equiv \bigl\{ x^n : |\overline{H}(x^n) - H(X)| \le \delta \bigr\}.
--   $$
--
--   **Formalization Note.** `WildeQIT.IsTypicalSeq p δ x` is the predicate and `WildeQIT.typicalSet p n δ : Finset (Fin n → α)` the set (a `Finset.filter` of all sequences); `mem_typicalSet` unfolds membership. A sequence of probability zero has sample entropy $+\infty$ in the book and is never typical; because Lean's `Real.logb 2 0 = 0` would give it sample entropy $0$, the definition requires $p_{X^n}(x^n) > 0$ explicitly. This replaces the retired `WildeQIT_weakTypicalSet`, which lacked that condition.
-- source:
--   Wilde, Quantum Information Theory 2nd ed. (Cambridge 2017; arXiv:1106.1445v8), Definition 14.2.3, §Weak Typicality, LaTeX label def-ct:weak-typ (roster-items.csv line 25025); and Definition 14.2.2 (Typical Sequence), line 25017.

import Definitions.Def_WildeQIT_sampleEntropy

/-!
Wilde, *Quantum Information Theory* (2nd ed.), Definition 14.2.2 (Typical sequence) and
Definition 14.2.3 (Typical set): a sequence `xⁿ` is `δ`-typical if its sample entropy is
`δ`-close to `H(X)`; the `δ`-typical set is `T_δ^{Xⁿ} ≡ { xⁿ : |H̄(xⁿ) − H(X)| ≤ δ }`.
A sequence of probability zero has sample entropy `+∞` in the book and is never typical; since
Lean's `Real.logb 2 0 = 0` would give it sample entropy `0`, the definition requires
`p_{Xⁿ}(xⁿ) > 0` explicitly. (Replaces the retired `WildeQIT_weakTypicalSet`.)
-/

namespace WildeQIT

variable {α : Type} [Fintype α]

/-- Definition 14.2.2. `x` is a `δ`-typical sequence for the source `p`: it has positive
probability and `|H̄(x) − H(X)| ≤ δ`. -/
def IsTypicalSeq (p : FinDist α) (δ : ℝ) {n : ℕ} (x : Fin n → α) : Prop :=
  0 < (p.iid n).prob x ∧ |sampleEntropy p x - entropy p| ≤ δ

/-- Definition 14.2.3. The `δ`-typical set `T_δ^{Xⁿ}` of length-`n` sequences. -/
noncomputable def typicalSet (p : FinDist α) (n : ℕ) (δ : ℝ) : Finset (Fin n → α) :=
  Finset.univ.filter fun x => 0 < (p.iid n).prob x ∧ |sampleEntropy p x - entropy p| ≤ δ

theorem mem_typicalSet {p : FinDist α} {n : ℕ} {δ : ℝ} {x : Fin n → α} :
    x ∈ typicalSet p n δ ↔ 0 < (p.iid n).prob x ∧ |sampleEntropy p x - entropy p| ≤ δ := by
  simp only [typicalSet, Finset.mem_filter, Finset.mem_univ, true_and]

end WildeQIT


