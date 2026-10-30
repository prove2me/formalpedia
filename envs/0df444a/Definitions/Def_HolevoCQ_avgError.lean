-- Prove2me | Definitions.Def_HolevoCQ_avgError
-- name    : HolevoCQ_avgError
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T03:14:54.565421+00:00
-- url     : https://prove2.me/theorems/8af05e0b-9509-4a24-8556-5847bf18516a
-- title:
--   Average error probability $P_{er}=\frac1N\sum_k[1-\mathrm{Tr}S_{u_k}X_k]$
-- statement:
--   For a code of size $N$ with transmitted states $S_{u_1},\dots,S_{u_N}$ and decision operators $X_1,\dots,X_N$, the average error probability is
--
--   $$
--   P_{er}=\frac1N\sum_{k=1}^N\big[1-\mathrm{Tr}\,S_{u_k}X_k\big].
--   $$
--
--   The evasion outcome $X_0$ counts as an error.
--
--   **Formalization Note** The code is indexed by positions $k$, so the words may repeat. The trace is the real part of the matrix trace. At $N=0$ Lean's $1/0=0$ gives the value $0$; all statements about codes in the mission use sizes $N\ge1$.
-- source:
--   Holevo, The Capacity of Quantum Channel with General Signal States, arXiv:quant-ph/9611023v1, p.2

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Information

open QAlgorithms

namespace HolevoCQ

/-- Holevo, *The Capacity of Quantum Channel with General Signal States*,
arXiv:quant-ph/9611023v1, p.2: the average error probability of a code,
`P_er = (1/N) Σ_{k=1}^N [1 − Tr S_{u_k} X_k]`, here for the list of transmitted states
`T k = S_{u_k}` and decision operators `X k`.

**Formalization Note.** The code is indexed by its position `k : Fin N`, so code words may
repeat. `Tr S X` is the real part of the trace (`effectProb`). At `N = 0` the value is `0`
(`1/0 = 0` in Lean); every statement about codes in this mission has `1 ≤ N` or a size that is
at least `1`. -/
noncomputable def avgError {ι : Type} [Fintype ι] {N : ℕ} (T X : Fin N → Matrix ι ι ℂ) : ℝ :=
  (1 / (N : ℝ)) * ∑ k, (1 - effectProb (X k) (T k))

end HolevoCQ


