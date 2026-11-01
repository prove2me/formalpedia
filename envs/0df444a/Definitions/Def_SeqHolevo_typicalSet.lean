-- Prove2me | Definitions.Def_SeqHolevo_typicalSet
-- name    : SeqHolevo_typicalSet
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T17:57:26.909988+00:00
-- url     : https://prove2.me/theorems/118a63a5-5a2e-4288-aeb7-38eae7a8caca
-- title:
--   Set $T^{X^n}_\delta$ of $\delta$-typical sequences
-- statement:
--   For a probability vector $p_X$ on $\mathbb N$, the **sample entropy** of $x^n=(x_1,\dots,x_n)$ is $\overline H(x^n)=-\tfrac1n\log_2p_{X^n}(x^n)$ with $p_{X^n}(x^n)=\prod_ip_X(x_i)$, and $H(X)=-\sum_xp_X(x)\log_2p_X(x)$. The set of $\delta$-typical sequences is
--
--   $$T^{X^n}_\delta=\{x^n:\ |\overline H(x^n)-H(X)|\le\delta\}.$$
--
--   **Formalization Note** Logarithms are base 2 and $H(X)$ is the published `selfInformationMean`. A sequence of probability zero has $\overline H=+\infty$ and is not typical; the definition says so explicitly ($p_{X^n}(x^n)>0$), because Lean's $\log0=0$ would otherwise make it typical when $H(X)\le\delta$. At $n=0$ Lean reads $1/0$ as $0$.
-- source:
--   Wilde–Guha–Tan–Lloyd, Explicit capacity-achieving receivers for optical communication and quantum reading, arXiv:1202.0518v2, Appendix A, p.6

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P76

open QAlgorithms.Papers.Independent.Intakenext100.P76 (selfInformationMean)
open QAlgorithms.Papers.Independent.Information100.P63 (logTwo)

namespace SeqHolevo

/-- Wilde–Guha–Tan–Lloyd, *Explicit capacity-achieving receivers for optical communication and quantum reading*, arXiv:1202.0518v2, Appendix A, p.6 (PDF page): the set of `δ`-typical sequences
`T_δ^{Xⁿ} ≡ {xⁿ : |H̄(xⁿ) − H(X)| ≤ δ}`, with sample entropy
`H̄(xⁿ) ≡ −(1/n) log p_{Xⁿ}(xⁿ)`, `p_{Xⁿ}(xⁿ) = ∏_i p_X(x_i)`, and `H(X) ≡ −Σ_x p_X(x) log p_X(x)`.

**Formalization Note.** Labels are `ℕ` (a countable spectrum), logarithms are base 2 (`logTwo`;
the paper's typical-projector bounds are powers of 2), and `H(X)` is the published
`selfInformationMean p = Σ_x p_x (−log₂ p_x)` (`Intakenext100.P76`). The extra condition
`0 < p_{Xⁿ}(xⁿ)` is the reading of `log 0 = −∞`: a sequence of probability zero has infinite
sample entropy and is never typical, whereas Lean's `Real.log 0 = 0` would otherwise make it
typical whenever `H(X) ≤ δ`. At `n = 0` Lean's `1/0 = 0` gives `H̄ = 0` (the paper's `n` is a
blocklength `≥ 1`). -/
def typicalSet (p : ℕ → ℝ) (n : ℕ) (δ : ℝ) : Set (Fin n → ℕ) :=
  {xs | 0 < ∏ i, p (xs i) ∧
    |-(1 / (n : ℝ)) * logTwo (∏ i, p (xs i)) - selfInformationMean p| ≤ δ}

end SeqHolevo


