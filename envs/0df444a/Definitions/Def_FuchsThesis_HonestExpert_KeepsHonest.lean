-- Prove2me | Definitions.Def_FuchsThesis_HonestExpert_KeepsHonest
-- name    : FuchsThesis_HonestExpert_KeepsHonest
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T15:21:46.434861+00:00
-- url     : https://prove2.me/theorems/78dd89b5-f01d-4cd3-8ab0-53061e575bee
-- title:
--   Payoff functions that keep the expert honest
-- statement:
--   An expert whose knowledge of an experiment with outcomes $b = 1, \dots, n$ is the distribution $p$ reports a distribution $q$ and is paid $F_b(q_b)$ if outcome $b$ occurs, where $F_1, \dots, F_n$ are fixed real functions. His expected earnings are $\sum_k p_k F_k(q_k)$.
--
--   The family $F = (F_1, \dots, F_n)$ **keeps the expert honest** if reporting the truth never earns less in expectation than any other report:
--
--   $$\sum_{k=1}^{n} p_k F_k(q_k) \;\le\; \sum_{k=1}^{n} p_k F_k(p_k)$$
--
--   for all strictly positive $n$-point probability distributions $p$ and $q$. This is inequality (2.45)/(2.47) of the thesis, imposed for every pair of distributions; payoffs with this property are what are now called (strictly) proper scoring rules, and they are the subject of Aczél's characterization, Theorem 2.3.
--
--   **Formalization Note** The functions $F_k \colon [0,1] \to \mathbb R$ of (2.43) are typed $\mathbb R \to \mathbb R$; since every entry of a strictly positive distribution lies in $(0,1]$, values outside the unit interval never enter. Distributions with a zero entry are not quantified over.
-- source:
--   Fuchs, Distinguishability and Accessible Information in Quantum Theory, arXiv:quant-ph/9601020v1, §2.3, (2.43)–(2.45), p.20 (PDF p.29); (2.47), p.21 (PDF p.30)

import Mathlib
import Definitions.Def_FuchsThesis_HonestExpert_IsPosDist

namespace FuchsThesis.HonestExpert

/-- **A payoff scheme that keeps the expert honest.**
Fuchs, *Distinguishability and Accessible Information in Quantum Theory*, arXiv:quant-ph/9601020v1,
§2.3, (2.43)–(2.45), p.20 (PDF p.29), and (2.47), p.21 (PDF p.30): the expert is paid `F_b(p₁(b))`
if outcome `b` occurs after reporting `p₁`; the scheme keeps him honest when
`∑_k p_k F_k(q_k) ≤ ∑_k p_k F_k(p_k)` for all `n`-point distributions `p` (his true state of
knowledge) and `q` (any report).

`KeepsHonest F` says that this inequality holds for every pair of strictly positive `n`-point
probability distributions `p, q`.

**Formalization Note.** The payoff functions `F_k : [0, 1] → ℝ` of (2.43) are typed `ℝ → ℝ`; since
every entry of a strictly positive distribution lies in `(0, 1]` (and in `(0, 1)` once `n ≥ 2`),
values of `F_k` outside the unit interval never enter. Distributions with zero entries are not
quantified over (see `IsPosDist`). -/
def KeepsHonest {n : ℕ} (F : Fin n → ℝ → ℝ) : Prop :=
  ∀ p q : Fin n → ℝ, IsPosDist p → IsPosDist q →
    ∑ k, p k * F k (q k) ≤ ∑ k, p k * F k (p k)

end FuchsThesis.HonestExpert


