-- Prove2me | Definitions.Def_KatyushaNs_condAvg
-- name    : KatyushaNs_condAvg
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T00:48:46.858627+00:00
-- url     : https://prove2.me/theorems/a9cf6951-60da-4b3e-905f-ce76b4d617ff
-- title:
--   Conditional expectation over the next $M$ indices
-- statement:
--   For $n \ge 1$, a fixed prefix $p = (p_0, \dots, p_{N-1})$ of indices, $M \ge 0$ and a real quantity $X$ depending on an index sequence,
--   $$\mathbb{E}[X \mid p] = \frac{1}{n^M}\sum_{w \in \{1,\dots,n\}^M} X(p\,w),$$
--   where $p\,w$ is the concatenation, padded beyond $N + M$. This is the expectation of $X$ when the first $N$ indices are fixed to $p$ and the next $M$ are independent and uniform, as in the proof of Theorem 4.1, where "all the randomness in the first $s-1$ epochs are fixed and the only source of randomness comes from epoch $s$".
-- source:
--   Allen-Zhu, Katyusha: The First Direct Acceleration of Stochastic Gradient Methods, arXiv:1603.05953v6, Appendix C.1, p. 26

import Mathlib
import Definitions.Def_KatyushaNs_extendSeq

namespace KatyushaNs

/-- **Conditional expectation over the next `M` indices, given the first `N`.**
Allen-Zhu, *Katyusha: The First Direct Acceleration of Stochastic Gradient Methods*,
arXiv:1603.05953v6, Appendix C.1, p. 26 (PDF p. 27): "in the above inequality we have assumed
all the randomness in the first s − 1 epochs are fixed and the only source of randomness comes
from epoch s."

`condAvg hn p M X = (1/n^M) Σ_{w : Fin M → Fin n} X(p ++ w padded)`: with the first `N` indices
fixed to the prefix `p`, the expectation of `X` over the next `M` indices drawn independently and
uniformly from `Fin n`.

**Formalization Note.** `p ++ w` is `Fin.append p w`; the sequence is padded beyond `N + M` by
`extendSeq`. -/
noncomputable def condAvg {n : ℕ} (hn : 0 < n) {N : ℕ} (p : Fin N → Fin n) (M : ℕ)
    (X : (ℕ → Fin n) → ℝ) : ℝ :=
  (∑ w : Fin M → Fin n, X (extendSeq hn (Fin.append p w))) / (n : ℝ) ^ M

end KatyushaNs


