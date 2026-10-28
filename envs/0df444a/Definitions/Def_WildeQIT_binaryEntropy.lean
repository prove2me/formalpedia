-- Prove2me | Definitions.Def_WildeQIT_binaryEntropy
-- name    : WildeQIT_binaryEntropy
-- status  : Definition
-- author  : @nonlocally
-- created : 2026-09-07T03:50:31.184958+00:00
-- url     : https://prove2.me/theorems/a3ab4875-2244-4eb6-ad4f-1ecd0133c2e2
-- title:
--   Binary entropy function $h_2(p)$ (Definition 10.1.2)
-- statement:
--   **Definition 10.1.2 (Binary entropy).** The binary entropy of $p\in[0,1]$ is
--
--   $$
--   h_2(p) \equiv -p\log p - (1-p)\log(1-p),
--   $$
--
--   with the logarithm taken base $2$ and the convention $0\log 0=0$, so that $h_2(0)=h_2(1)=0$.
--
--   The binary entropy is the entropy of a Bernoulli random variable with parameter $p$; it is the function that appears in Fano's inequality (Theorem 10.7.3), in the Zhang–Audenaert continuity bound (Theorem 10.7.4), and throughout the rate expressions of classical and quantum Shannon theory.
--
--   **Formalization Note.** `WildeQIT.binaryEntropy p` is defined for every real $p$ by the same formula, $-(p\log_2 p) - (1-p)\log_2(1-p)$, using `Real.logb 2`. Since Mathlib sets `Real.logb 2 0 = 0`, the endpoint values $h_2(0)=h_2(1)=0$ hold automatically; outside $[0,1]$ the formula returns a real number that carries no meaning (Mathlib's `Real.log` of a negative number is the log of its absolute value). Statements that use $h_2$ carry the hypothesis $p\in[0,1]$ where it matters.
-- source:
--   Wilde, Quantum Information Theory, 2nd ed. (Cambridge University Press, 2017; arXiv:1106.1445v8), Chapter 10 (Classical Information and Entropy), §The Binary Entropy Function, Definition 10.1.2 (book source roster-items.csv line 16236).

import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
Wilde, *Quantum Information Theory* (2nd ed.), Definition 10.1.2 (Binary entropy):
`h₂(p) ≡ -p log p - (1-p) log(1-p)` for `p ∈ [0,1]`, logarithm base 2.
-/

namespace WildeQIT

/-- Definition 10.1.2. The binary entropy function `h₂(p) = -p log₂ p - (1-p) log₂ (1-p)`.
Defined for every real `p` (Wilde: `p ∈ [0,1]`); at `p = 0` and `p = 1` the convention
`0 log 0 = 0` is automatic since `Real.logb 2 0 = 0`. -/
noncomputable def binaryEntropy (p : ℝ) : ℝ :=
  -(p * Real.logb 2 p) - (1 - p) * Real.logb 2 (1 - p)

end WildeQIT


