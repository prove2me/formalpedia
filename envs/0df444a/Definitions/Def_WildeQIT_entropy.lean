-- Prove2me | Definitions.Def_WildeQIT_entropy
-- name    : WildeQIT_entropy
-- status  : Definition
-- author  : @nonlocally
-- created : 2026-09-07T03:50:30.553399+00:00
-- url     : https://prove2.me/theorems/9ea1e608-da53-461a-bccf-edb3e190f544
-- title:
--   Entropy $H(X)$ of a random variable (Definition 10.1.1)
-- statement:
--   **Definition 10.1.1 (Entropy).** The entropy of a discrete random variable $X$ with probability distribution $p_X(x)$ on a finite alphabet $\mathcal{X}$ is
--
--   $$
--   H(X) \equiv -\sum_{x\in\mathcal{X}} p_X(x)\,\log\bigl(p_X(x)\bigr),
--   $$
--
--   with the logarithm taken base $2$ (so that entropy is measured in bits), and with the convention $0\log 0 = 0$ for letters of probability zero.
--
--   Entropy quantifies the surprise, or information content, of a random variable on average: $H(X)$ is the expected value of the information content $i(x)=-\log p_X(x)$ of the outcome $x$. It is the central quantity of classical information theory and every other quantity of Wilde's Chapter 10 (conditional entropy, joint entropy, mutual information, relative entropy) is built from it.
--
--   **Formalization Note.** `WildeQIT.entropy p` is $-\sum_x p(x)\,\log_2 p(x)$ as a real number, for `p : WildeQIT.FinDist α` a probability distribution on a finite alphabet `α`. The logarithm is `Real.logb 2`. The convention $0\log 0=0$ is automatic, because Mathlib defines `Real.logb 2 0 = 0`, so a letter with $p(x)=0$ contributes $0\cdot 0 = 0$ to the sum.
-- source:
--   Wilde, Quantum Information Theory, 2nd ed. (Cambridge University Press, 2017; arXiv:1106.1445v8), Chapter 10 (Classical Information and Entropy), §Entropy of a Random Variable, Definition 10.1.1 (book source roster-items.csv line 16182); log base 2 and 0 log 0 = 0 conventions stated in §10.1.

import Definitions.Def_WildeQIT_FinDist
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
Wilde, *Quantum Information Theory* (2nd ed.), Definition 10.1.1 (Entropy):
`H(X) ≡ -∑_x p_X(x) log p_X(x)`, logarithm base 2 (bits), with the convention `0 log 0 = 0`.
-/

namespace WildeQIT

/-- Definition 10.1.1. The (Shannon) entropy of a random variable with distribution `p`,
in bits: `H(X) = -∑_x p(x) log₂ p(x)`. The convention `0 log 0 = 0` holds automatically,
because `Real.logb 2 0 = 0`. -/
noncomputable def entropy {α : Type} [Fintype α] (p : FinDist α) : ℝ :=
  -∑ x, p.prob x * Real.logb 2 (p.prob x)

end WildeQIT


