-- Prove2me | Definitions.Def_PacketRouting_CongDil_Recurrences
-- name    : PacketRouting_CongDil_Recurrences
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T11:44:42.855025+00:00
-- url     : https://prove2.me/theorems/66481b61-a023-4e4b-b767-0a4366cb6f18
-- title:
--   §3.2, p. 13 — the frame sizes I^(i), relative congestions r^(i) and the iterated logarithm log* d
-- statement:
--   The proof of Theorem 3.4 refines schedules $S_1,S_2,\dots$; schedule $S_i$ has relative congestion at most $r^{(i)}$ in every frame of size $I^{(i)}$ or greater. On p. 13 these parameters are given by the recurrences (with $\log=\log_2$)
--   $$
--   r^{(i+1)}=\begin{cases}1 & i=0\\ r^{(i)}\bigl(1+O(1)/\sqrt{\log I^{(i)}}\bigr) & i>0\end{cases}
--   \qquad
--   I^{(i+1)}=\begin{cases}\log d & i=0\\ \log^5 I^{(i)} & i>0.\end{cases}
--   $$
--   This module defines, for a natural number $d$ and a real constant $\kappa$ standing for the $O(1)$:
--
--   1. the frame sizes $I^{(1)}=\log_2 d$ and $I^{(i+1)}=(\log_2 I^{(i)})^5$ for $i\ge 1$;
--   2. the relative congestions $r^{(1)}=1$ and $r^{(i+1)}=r^{(i)}\bigl(1+\kappa/\sqrt{\log_2 I^{(i)}}\bigr)$ for $i\ge1$;
--   3. the **iterated logarithm** $\log^* x$, the least number of applications of $\log_2$ that bring $x$ down to at most $1$.
--
--   **Formalization Note** Indices start at $1$ as in the paper; the value at index $0$ is unused (set to $I^{(0)}=0$, $r^{(0)}=1$). Real `Real.logb 2` and `Real.sqrt` are total functions (value $0$ on non-positive arguments); the theorem that uses these sequences only evaluates them at indices where $I^{(i)}$ exceeds a large threshold, where both are positive.
-- source:
--   Leighton, Maggs & Rao, Packet routing and job-shop scheduling in O(congestion + dilation) steps, authors' manuscript (preprint of Combinatorica 14 (1994), DOI 10.1007/BF01215349), p. 13, the recurrences for r^(i+1) and I^(i+1)

import Mathlib

namespace PacketRouting.CongDil

/-- The **iterated logarithm** `log* x` (base 2): the least number `n` of applications of
`log₂` that bring `x` down to at most `1`. (`log* x = 0` for `x ≤ 1`.) The set is nonempty for
every real `x`, so the infimum is attained. -/
noncomputable def logStar (x : ℝ) : ℕ :=
  sInf {n : ℕ | (Real.logb 2)^[n] x ≤ 1}

/-- The frame sizes `I^{(i)}` of the schedules `S_i` (Leighton–Maggs–Rao, p. 13):
`I^{(1)} = log d` and `I^{(i+1)} = log⁵ I^{(i)}` for `i > 0`, with `log = log₂`. Indexing is
the paper's, starting at `1`; the value at index `0` is not used by the paper and is set to `0`. -/
noncomputable def frameSizeSeq (d : ℕ) : ℕ → ℝ
  | 0 => 0
  | 1 => Real.logb 2 d
  | n + 2 => (Real.logb 2 (frameSizeSeq d (n + 1))) ^ 5

/-- The relative congestions `r^{(i)}` of the schedules `S_i` (p. 13): `r^{(1)} = 1` and
`r^{(i+1)} = r^{(i)} (1 + κ / √(log I^{(i)}))` for `i > 0`, where the constant `κ > 0` stands for
the paper's `O(1)`. Index `0` is unused and set to `1`. -/
noncomputable def relCongSeq (κ : ℝ) (d : ℕ) : ℕ → ℝ
  | 0 => 1
  | 1 => 1
  | n + 2 => relCongSeq κ d (n + 1) *
      (1 + κ / Real.sqrt (Real.logb 2 (frameSizeSeq d (n + 1))))

end PacketRouting.CongDil


