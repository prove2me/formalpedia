-- Prove2me | Definitions.Def_WildeQIT_sampleEntropy
-- name    : WildeQIT_sampleEntropy
-- status  : Definition
-- author  : @nonlocally
-- created : 2026-09-07T07:29:00.894715+00:00
-- url     : https://prove2.me/theorems/8dcabf1a-3191-4d94-a2b5-1a921d61f03f
-- title:
--   Sample entropy $\overline{H}(x^n)$ (Definition 14.2.1)
-- statement:
--   Throughout Chapter 14 an information source emits $n$ independent, identically distributed copies of a random variable $X$ with distribution $p_X$ on a finite alphabet $\mathcal{X}$; a realization is a sequence $x^n = x_1\cdots x_n$ (Lean: `Fin n → α`), with $p_{X^n}(x^n) = \prod_{i=1}^n p_X(x_i)$. Entropies are in bits.
--
--   **Definition 14.2.1 (Sample entropy).** The sample entropy $\overline{H}(x^n)$ of a sequence $x^n$ with respect to a probability distribution $p_X(x)$ is
--
--   $$
--   \overline{H}(x^n) \equiv -\frac{1}{n}\log\bigl(p_{X^n}(x^n)\bigr), \qquad p_{X^n}(x^n) = \prod_{i=1}^n p_X(x_i).
--   $$
--
--   The sample entropy is the empirical counterpart of $H(X)$: by the law of large numbers it concentrates around $H(X)$, which is the origin of typicality.
--
--   **Formalization Note.** `WildeQIT.sampleEntropy p x = -(1/n) * Real.logb 2 ((p.iid n).prob x)`; for $n = 0$ Lean's $1/0 = 0$ makes it $0$, and for a sequence of probability $0$ the value is $0$ (`Real.logb 2 0 = 0`) rather than $+\infty$.
-- source:
--   Wilde, Quantum Information Theory 2nd ed. (Cambridge 2017; arXiv:1106.1445v8), Definition 14.2.1, §Weak Typicality (roster-items.csv line 25003).

import Definitions.Def_WildeQIT_iid
import Definitions.Def_WildeQIT_entropy

/-!
Wilde, *Quantum Information Theory* (2nd ed.), Definition 14.2.1 (Sample entropy):
`H̄(xⁿ) ≡ -(1/n) log p_{Xⁿ}(xⁿ)`, where `p_{Xⁿ}(xⁿ) = ∏ᵢ p_X(xᵢ)`; logarithm base 2.
-/

namespace WildeQIT

/-- Definition 14.2.1. The sample entropy of the sequence `x` with respect to `p`:
`H̄(x) = -(1/n) log₂ (∏ᵢ p(xᵢ))`. -/
noncomputable def sampleEntropy {α : Type} [Fintype α] (p : FinDist α) {n : ℕ} (x : Fin n → α) : ℝ :=
  -(1 / (n : ℝ)) * Real.logb 2 ((p.iid n).prob x)

end WildeQIT


