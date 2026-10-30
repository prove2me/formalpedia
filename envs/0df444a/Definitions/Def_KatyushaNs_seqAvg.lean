-- Prove2me | Definitions.Def_KatyushaNs_seqAvg
-- name    : KatyushaNs_seqAvg
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T00:48:16.49924+00:00
-- url     : https://prove2.me/theorems/af7ce918-2eff-4d79-8089-8e78c87d749a
-- title:
--   Expectation over $N$ uniform i.i.d. indices
-- statement:
--   For $n \ge 1$, $N \ge 0$ and a real quantity $X$ depending on an index sequence,
--   $$\mathbb{E}_N[X] = \frac{1}{n^N}\sum_{w \in \{1,\dots,n\}^N} X(w),$$
--   where $X$ is evaluated at the padded sequence of $w$. This is the expectation of $X$ when the indices of iterations $0, \dots, N-1$ are drawn independently and uniformly from $\{1, \dots, n\}$, as in line 10 of Algorithm 2, provided $X$ depends only on those indices.
--
--   **Formalization Note** The expectation is a finite uniform average; no measure theory is involved.
-- source:
--   Allen-Zhu, Katyusha: The First Direct Acceleration of Stochastic Gradient Methods, arXiv:1603.05953v6, Algorithm 2, line 10, p. 15; Theorem 4.1, p. 15

import Mathlib
import Definitions.Def_KatyushaNs_extendSeq

namespace KatyushaNs

/-- **Expectation over `N` i.i.d. uniform indices.**
Allen-Zhu, *Katyusha: The First Direct Acceleration of Stochastic Gradient Methods*,
arXiv:1603.05953v6, Algorithm 2 line 10, p. 15 (PDF p. 16): in each iteration "i is randomly
chosen from {1, 2, …, n}"; `E[·]` in Theorem 4.1 and Appendix C.1 is over these choices.

`seqAvg hn N X = (1/n^N) Σ_{w : {0,…,N−1} → {0,…,n−1}} X(w padded)`: the expectation of `X` when
the indices of iterations `0, …, N − 1` are independent and uniform on `Fin n`.

**Formalization Note.** The expectation is the finite uniform average over all `n^N` index
sequences (no measure theory). `X` is evaluated at the padded sequence `extendSeq hn w`; it is the
expectation of `X` whenever `X` depends only on the first `N` indices. -/
noncomputable def seqAvg {n : ℕ} (hn : 0 < n) (N : ℕ) (X : (ℕ → Fin n) → ℝ) : ℝ :=
  (∑ w : Fin N → Fin n, X (extendSeq hn w)) / (n : ℝ) ^ N

end KatyushaNs


