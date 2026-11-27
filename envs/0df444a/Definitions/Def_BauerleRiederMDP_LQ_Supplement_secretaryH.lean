-- Prove2me | Definitions.Def_BauerleRiederMDP_LQ_Supplement_secretaryH
-- name    : BauerleRiederMDP_LQ_Supplement_secretaryH
-- status  : Definition
-- author  : @iris
-- created : 2026-11-26T23:45:44.473447+00:00
-- url     : https://prove2.me/theorems/4cd78559-9e02-41a2-b009-577fa651e6af
-- title:
--   The function $h$ of the secretary problem
-- statement:
--   **The function $h$ of the secretary problem** (Bäuerle & Rieder, *Markov Decision Processes with Applications to Finance* (2011), §10.3.3, p.322, PDF 330): $h(x) := 1/x + 1/(x+1) + \dots  + 1/(N-1)$, $x = 1, \dots , N - 1$.
--
--   **Formalization Note.** `secretaryH N x = ∑_{j = x}^{N−1} 1/j` as a real sum over `Finset.Ico x N`; only $1 \le  x \le  N - 1$ is used.
-- source:
--   Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), §10.3.3, p.322, PDF 330

import Mathlib

namespace BauerleRiederMDP.LQ.Supplement

/-- **The function `h` of the secretary problem** (Bäuerle & Rieder, *Markov Decision Processes
with Applications to Finance* (2011), §10.3.3, p.322, PDF 330):
`h(x) := 1/x + 1/(x+1) + … + 1/(N−1)`, `x = 1, …, N − 1`.

**Formalization Note.** `secretaryH N x = ∑_{j = x}^{N−1} 1/j` as a real sum over `Finset.Ico x N`;
only `1 ≤ x ≤ N − 1` is used. -/
noncomputable def secretaryH (N x : ℕ) : ℝ :=
  ∑ j ∈ Finset.Ico x N, (1 : ℝ) / j

end BauerleRiederMDP.LQ.Supplement


