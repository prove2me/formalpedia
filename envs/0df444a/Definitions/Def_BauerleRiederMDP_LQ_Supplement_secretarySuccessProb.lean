-- Prove2me | Definitions.Def_BauerleRiederMDP_LQ_Supplement_secretarySuccessProb
-- name    : BauerleRiederMDP_LQ_Supplement_secretarySuccessProb
-- status  : Definition
-- author  : @iris
-- created : 2026-11-26T23:46:55.973823+00:00
-- url     : https://prove2.me/theorems/78cb0c89-d3f0-5cf6-97fa-0056bf991df2
-- title:
--   The probability of choosing the best candidate
-- statement:
--   **The probability of choosing the best candidate** (Bäuerle & Rieder, *Markov Decision Processes with Applications to Finance* (2011), §10.3.3, p.321, PDF 329, $\mathbb P (Z_{X_\tau } = N)$): for a stopping rule $\tau $, the probability, under the uniform distribution on the permutations $\sigma $ of the absolute ranks, that the accepted candidate $\tau (\sigma )$ is the best one (absolute rank $N - 1$).
--
--   **Formalization Note.** The uniform law on `Equiv.Perm (Fin N)` gives each permutation mass $1/N!$, so the probability is a ratio of cardinalities, as a real number.
-- source:
--   Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), §10.3.3, p.321, PDF 329, `ℙ(Z_{X_τ} = N)`

import Mathlib

namespace BauerleRiederMDP.LQ.Supplement

/-- **The probability of choosing the best candidate** (Bäuerle & Rieder, *Markov Decision
Processes with Applications to Finance* (2011), §10.3.3, p.321, PDF 329, `ℙ(Z_{X_τ} = N)`): for a
stopping rule `τ`, the probability, under the uniform distribution on the permutations `σ` of the
absolute ranks, that the accepted candidate `τ(σ)` is the best one (absolute rank `N − 1`).

**Formalization Note.** The uniform law on `Equiv.Perm (Fin N)` gives each permutation mass
`1/N!`, so the probability is a ratio of cardinalities, as a real number. -/
noncomputable def secretarySuccessProb (N : ℕ) (τ : Equiv.Perm (Fin N) → Fin N) : ℝ :=
  ((Finset.univ.filter fun σ : Equiv.Perm (Fin N) => (σ (τ σ)).val + 1 = N).card : ℝ) /
    (Nat.factorial N : ℝ)

end BauerleRiederMDP.LQ.Supplement


