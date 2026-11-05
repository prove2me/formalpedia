-- Prove2me | Definitions.Def_DHRUniq_Majorizes
-- name    : DHRUniq_Majorizes
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:32:42.686781+00:00
-- url     : https://prove2.me/theorems/7e62f242-3c46-49b3-b554-5b683531aee6
-- title:
--   Majorization of decreasing probability sequences
-- statement:
--   Let $(p_i)_{i=1}^{m_1}$ and $(q_i)_{i=1}^{m_2}$ be probability distributions arranged in decreasing order. Then $(q_i)$ **majorizes** $(p_i)$, written $(q_i)\succ(p_i)$, if for all $k\le\min\{m_1,m_2\}$,
--
--   $$
--   \sum_{i=1}^kq_i\ge\sum_{i=1}^kp_i.
--   $$
--
--   The two sequences may have different lengths. Majorization governs which pure states convert into which by LQCC operations.
--
--   **Formalization Note** Sequences are lists. The decreasing order and normalization are preconditions of the definition rather than clauses of the predicate; the mission applies it only to sequences that have them.
-- source:
--   Donald, Horodecki, Rudolph, The uniqueness theorem for entanglement measures, arXiv:quant-ph/0105017v2, Definition 6, p. 6, eq. (10)

import Mathlib

namespace DHRUniq

/-- **Majorization** (Donald, Horodecki, Rudolph, *The uniqueness theorem for entanglement measures*, arXiv:quant-ph/0105017v2, Definition 6, p. 6): for probability distributions
`(p_i)_{i=1}^{m_1}` and `(q_i)_{i=1}^{m_2}` arranged in decreasing order, `(q_i)` majorizes `(p_i)`
if `∑_{i=1}^k q_i ≥ ∑_{i=1}^k p_i` for all `k ≤ min{m_1, m_2}` (eq. (10)).

**Formalization Note** The sequences are lists, so that they may have different lengths, and
`Majorizes q p` is `q ≻ p`. Being decreasing probability distributions is the precondition of the
definition, not part of the predicate: the mission applies `Majorizes` only to `schmidtCoeffs` and
to the antitone Schmidt coefficients of Theorem 7. For `k = 0` the inequality is `0 ≤ 0`. -/
def Majorizes (q p : List ℝ) : Prop :=
  ∀ k ≤ min p.length q.length, (p.take k).sum ≤ (q.take k).sum

end DHRUniq


