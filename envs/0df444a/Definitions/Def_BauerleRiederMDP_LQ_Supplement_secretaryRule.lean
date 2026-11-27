-- Prove2me | Definitions.Def_BauerleRiederMDP_LQ_Supplement_secretaryRule
-- name    : BauerleRiederMDP_LQ_Supplement_secretaryRule
-- status  : Definition
-- author  : @iris
-- created : 2026-11-26T23:46:45.548211+00:00
-- url     : https://prove2.me/theorems/bd772cf8-f3dd-4b99-9039-3a6b6ee4bab4
-- title:
--   The threshold rule of the secretary problem
-- statement:
--   **The threshold rule of the secretary problem** (Bäuerle & Rieder, *Markov Decision Processes with Applications to Finance* (2011), Theorem 10.3.3, p.323, PDF 331): interview the first $k$ candidates and reject them all; afterwards take the first candidate who is better than all her predecessors.
--
--   **Formalization Note.** Candidates are $0, \dots , N - 1$ ($j$ is the book's candidate $j + 1$), so the rejected ones are $j < k$. If no candidate $j \ge  k$ is better than her predecessors (the book's $X_\tau  = N + 1$, reward $0$), the rule ends at the last candidate, who is then not the best, so the probability of success is the same. $hN : 0 < N$ supplies that last candidate.
-- source:
--   Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), Theorem 10.3.3, p.323, PDF 331

import Mathlib

namespace BauerleRiederMDP.LQ.Supplement

open Classical in
/-- **The threshold rule of the secretary problem** (Bäuerle & Rieder, *Markov Decision Processes
with Applications to Finance* (2011), Theorem 10.3.3, p.323, PDF 331): interview the first `k`
candidates and reject them all; afterwards take the first candidate who is better than all her
predecessors.

**Formalization Note.** Candidates are `0, …, N − 1` (`j` is the book's candidate `j + 1`), so the
rejected ones are `j < k`. If no candidate `j ≥ k` is better than her predecessors (the book's
`X_τ = N + 1`, reward `0`), the rule ends at the last candidate, who is then not the best, so the
probability of success is the same. `hN : 0 < N` supplies that last candidate. -/
noncomputable def secretaryRule (N k : ℕ) (hN : 0 < N) (σ : Equiv.Perm (Fin N)) : Fin N :=
  let S := Finset.univ.filter fun j : Fin N => k ≤ j.val ∧ ∀ i : Fin N, i < j → σ i < σ j
  if h : S.Nonempty then S.min' h else ⟨N - 1, by omega⟩

end BauerleRiederMDP.LQ.Supplement


