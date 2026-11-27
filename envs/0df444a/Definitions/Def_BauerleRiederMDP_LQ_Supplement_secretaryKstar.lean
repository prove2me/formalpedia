-- Prove2me | Definitions.Def_BauerleRiederMDP_LQ_Supplement_secretaryKstar
-- name    : BauerleRiederMDP_LQ_Supplement_secretaryKstar
-- status  : Definition
-- author  : @iris
-- created : 2026-11-26T23:46:29.977941+00:00
-- url     : https://prove2.me/theorems/e850d503-ac1f-4331-9e45-9f7dadcc7201
-- title:
--   The threshold $k^*$ of the secretary problem
-- statement:
--   **The threshold $k^*$ of the secretary problem** (Bäuerle & Rieder, *Markov Decision Processes with Applications to Finance* (2011), eq. (10.5), p.322, PDF 330): $k^* := \inf  {k \in  {1, \dots , N - 2} | h(k) > 1 \ge  h(k + 1)}$.
--
--   **Formalization Note.** `sInf` on $\mathbb N $. For $N > 2$ the set is nonempty ($h$ is decreasing with $h(1) > 1 > h(N - 1)$, p.322), so the infimum is attained and is not the junk value $0$.
-- source:
--   Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), eq. (10.5), p.322, PDF 330

import Mathlib
import Definitions.Def_BauerleRiederMDP_LQ_Supplement_secretaryH

namespace BauerleRiederMDP.LQ.Supplement

/-- **The threshold `k*` of the secretary problem** (Bäuerle & Rieder, *Markov Decision Processes
with Applications to Finance* (2011), eq. (10.5), p.322, PDF 330):
`k* := inf {k ∈ {1, …, N − 2} | h(k) > 1 ≥ h(k + 1)}`.

**Formalization Note.** `sInf` on `ℕ`. For `N > 2` the set is nonempty (`h` is decreasing with
`h(1) > 1 > h(N − 1)`, p.322), so the infimum is attained and is not the junk value `0`. -/
noncomputable def secretaryKstar (N : ℕ) : ℕ :=
  sInf {k : ℕ | 1 ≤ k ∧ k ≤ N - 2 ∧ 1 < secretaryH N k ∧ secretaryH N (k + 1) ≤ 1}

end BauerleRiederMDP.LQ.Supplement


