-- Prove2me | Definitions.Def_BauerleRiederMDP_LQ_Supplement_IsRelRankStoppingTime
-- name    : BauerleRiederMDP_LQ_Supplement_IsRelRankStoppingTime
-- status  : Definition
-- author  : @iris
-- created : 2026-11-26T23:09:50.1265+00:00
-- url     : https://prove2.me/theorems/1b90c7eb-70b0-4352-8f30-8a63e249e9bf
-- title:
--   A stopping rule of the secretary problem
-- statement:
--   **A stopping rule of the secretary problem** (Bäuerle & Rieder, *Markov Decision Processes with Applications to Finance* (2011), §10.3.3, pp.319–321, PDF 327–329): $N$ candidates arrive in the order of a uniformly random permutation $\sigma $ of the absolute ranks ($\sigma  j$ is the absolute rank of the candidate interviewed at time $j$, rank $N - 1$ = the best); after interviewing candidate $j$ only the relative ranks of the first $j + 1$ candidates are known, and the decision to accept candidate $j$ must be based on them. A rule $\tau $ (the index of the accepted candidate) is admissible if the event ${\tau  = j}$ is determined by the relative order of the first $j + 1$ candidates.
--
--   **Formalization Note.** Times are $0, \dots , N - 1$ ($Fin N$; candidate $j$ is the book's candidate $j + 1$); a rule always accepts some candidate, so the book's $\tau  \le  N - 1$ is built in. The information at time $j$ is the order relation $\sigma  i < \sigma  i'$ for $i, i' \le  j$. This is the class of stopping times of the book's problem $\sup _{\tau  \le  N-1} \mathbb P (Z_{X_\tau } = N)$: a stopping time of the record chain $(X_n)$ is a stopping rule on the candidates, and conversely only stopping at a record can be successful.
-- source:
--   Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), §10.3.3, pp.319–321, PDF 327–329

import Mathlib

namespace BauerleRiederMDP.LQ.Supplement

/-- **A stopping rule of the secretary problem** (Bäuerle & Rieder, *Markov Decision Processes with
Applications to Finance* (2011), §10.3.3, pp.319–321, PDF 327–329): `N` candidates arrive in the
order of a uniformly random permutation `σ` of the absolute ranks (`σ j` is the absolute rank of the
candidate interviewed at time `j`, rank `N − 1` = the best); after interviewing candidate `j` only
the relative ranks of the first `j + 1` candidates are known, and the decision to accept candidate
`j` must be based on them. A rule `τ` (the index of the accepted candidate) is admissible if the
event `{τ = j}` is determined by the relative order of the first `j + 1` candidates.

**Formalization Note.** Times are `0, …, N − 1` (`Fin N`; candidate `j` is the book's candidate
`j + 1`); a rule always accepts some candidate, so the book's `τ ≤ N − 1` is built in. The
information at time `j` is the order relation `σ i < σ i'` for `i, i' ≤ j`. This is the class of
stopping times of the book's problem `sup_{τ ≤ N−1} ℙ(Z_{X_τ} = N)`: a stopping time of the record
chain `(X_n)` is a stopping rule on the candidates, and conversely only stopping at a record can be
successful. -/
def IsRelRankStoppingTime (N : ℕ) (τ : Equiv.Perm (Fin N) → Fin N) : Prop :=
  ∀ (σ σ' : Equiv.Perm (Fin N)) (j : Fin N),
    (∀ i i' : Fin N, i ≤ j → i' ≤ j → (σ i < σ i' ↔ σ' i < σ' i')) → (τ σ = j ↔ τ σ' = j)

end BauerleRiederMDP.LQ.Supplement


