-- Prove2me | Definitions.Def_FuchsThesis_HonestExpert_IsPosDist
-- name    : FuchsThesis_HonestExpert_IsPosDist
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T15:20:53.676445+00:00
-- url     : https://prove2.me/theorems/1ce234d4-27a0-428d-99cf-40f5f3ceaa9c
-- title:
--   Strictly positive $n$-point probability distributions
-- statement:
--   Let $n$ be a natural number. A vector $p = (p_1, \dots, p_n)$ of real numbers is a **strictly positive $n$-point probability distribution** if
--
--   $$p_k > 0 \quad (k = 1, \dots, n), \qquad \sum_{k=1}^{n} p_k = 1 .$$
--
--   These are the distributions over which the honest-expert problem of §2.3 is posed in this mission: an expert's state of knowledge $p_0(b)$ and his report $p_1(b)$ about an experiment with outcomes $b = 1, \dots, n$.
--
--   **Formalization Note** Outcomes are indexed by `Fin n`. Entries are required to be strictly positive, because the logarithmic payoff $\alpha \ln p + \gamma_k$ of Theorem 2.3 is undefined at $p = 0$; this is the reading under which Theorem 2.3 is stated (see the goal theorem).
-- source:
--   Fuchs, Distinguishability and Accessible Information in Quantum Theory, arXiv:quant-ph/9601020v1, §2.3, (2.43)–(2.45), p.20 (PDF p.29); Theorem 2.3, p.21 (PDF p.30)

import Mathlib

namespace FuchsThesis.HonestExpert

/-- **Strictly positive `n`-point probability distributions.**
Fuchs, *Distinguishability and Accessible Information in Quantum Theory*, arXiv:quant-ph/9601020v1,
§2.3, (2.43)–(2.45), p.20 (PDF p.29), and Theorem 2.3, p.21 (PDF p.30): the expert's distributions
`p₀(b), p₁(b)`, `b = 1, …, n`, "`n`-point probability distributions `(p₁, …, pₙ)`".

`IsPosDist p` says that `p : Fin n → ℝ` has every entry strictly positive and total mass one.

**Formalization Note.** Outcomes `b = 1, …, n` are indexed by `Fin n` (`0, …, n − 1`). Entries are
required to be strictly positive: this is the reading under which Theorem 2.3 is stated in this
mission, because the logarithmic payoff `α ln p + γ_k` is undefined at `p = 0`. -/
def IsPosDist {n : ℕ} (p : Fin n → ℝ) : Prop :=
  (∀ k, 0 < p k) ∧ ∑ k, p k = 1

end FuchsThesis.HonestExpert


