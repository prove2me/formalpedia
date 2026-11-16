-- Prove2me | Definitions.Def_UCalibDirichlet_Supplement_seq19
-- name    : UCalibDirichlet_Supplement_seq19
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T04:11:55.727744+00:00
-- url     : https://prove2.me/theorems/8f5cc4af-4fa3-440f-bd12-eeec7965cfd4
-- title:
--   The outcome sequence of Theorem 1.9: $T-K+1$ ones, then $2,\dots,K$
-- statement:
--   For $K\ge 1$ and $T\ge K$, the outcome sequence of Theorem 1.9 is
--   $$\underbrace{1,1,\dots,1}_{T-K+1\text{ ones}},\,2,\,3,\,\dots,\,K,$$
--   of length $T$: label $1$ in the first $T-K+1$ rounds, then each of the labels $2,\dots,K$ exactly once.
--
--   **Formalization Note** Rounds and labels are $0$-based: round $t\in\{0,\dots,T-1\}$ carries label index $0$ for $t\le T-K$ and label index $t-(T-K)$ otherwise, so the paper's label $j$ is index $j-1$. The definition takes a proof that $K>0$ so that label index $0$ exists.
-- source:
--   Frongillo, Luo, Mehta & Schneider, Near-Optimal Regret in U-Calibration for Every Proper Loss (manuscript, STOC 2027 submission), Theorem 1.9, p.6; proof of Theorem 1.9, p.34

import Mathlib

namespace UCalibDirichlet.Supplement

/-- **The outcome sequence of Theorem 1.9.** Frongillo, Luo, Mehta & Schneider (manuscript, STOC
2027 submission), Theorem 1.9, p.6: "for the outcome sequence `1, 1, …, 1` (`T − K + 1` ones),
`2, …, K`"; proof, p.34: "the label sequence is `(T − K + 1)` 1's followed by `2, 3, …, K`".

With 0-based rounds `t < T` and 0-based labels (`Fin K`, the paper's label `j` is index `j − 1`):
`seq19 K T t = 0` for `t ≤ T − K`, and `seq19 K T t = t − (T − K)` for `t > T − K`, i.e. the last
`K − 1` rounds carry the labels `1, …, K − 1` (the paper's `2, …, K`).

**Formalization Note.** The proof term `hK : 0 < K` only makes label `0` exist. The sequence is the
paper's when `T ≥ K`, the range used by Theorem 1.9. -/
def seq19 (K T : ℕ) (hK : 0 < K) (t : Fin T) : Fin K :=
  if h : t.val ≤ T - K then ⟨0, hK⟩ else ⟨t.val - (T - K), by omega⟩

end UCalibDirichlet.Supplement


