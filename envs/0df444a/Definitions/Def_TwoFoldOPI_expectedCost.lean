-- Prove2me | Definitions.Def_TwoFoldOPI_expectedCost
-- name    : TwoFoldOPI_expectedCost
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T22:45:55.757058+00:00
-- url     : https://prove2.me/theorems/6b6fe1e4-0566-4fa7-bb91-d284bea41e39
-- title:
--   Expected cost of repeating a trial until it accepts
-- statement:
--   For a trial program $T$ with $N$ qubits and $c$ classical bits, the expected charged work of one trial is $\sum_{\text{leaves}}\Pr(\text{leaf})\cdot\mathrm{work}(\text{leaf})$, where the work of an execution leaf counts its queries, gates, resets, measurements and classical steps. The number of trials until acceptance is geometric with mean $1/\Pr[\text{flag}=1]$, so the expected total cost of the restart loop is at most
--   $$\frac{N+c+\sum_{\text{leaves}}\Pr(\text{leaf})\,\mathrm{work}(\text{leaf})}{\Pr[\text{flag}=1]} .$$
--   This is the "expected gate complexity" of Theorem 5.30.
--
--   **Formalization Note** Space $N+c$ is charged once per expected trial, which can only increase the cost.
-- source:
--   Ragavan, Shutty, Quantum Algorithms for OPI Variants Beyond Locality and Classical Decodability, arXiv:2610.00502 (version held, sha256 ef050ec0…62605), §5.2, Theorem 5.30, p. 29; proof, p. 30

import Mathlib
import Definitions.Def_TwoFoldOPI_acceptProb

namespace TwoFoldOPI

open QAlgorithms QAlgorithms.OPI

/-- **Expected cost of "repeat the trial until it accepts".**
Ragavan, Shutty, *Quantum Algorithms for OPI Variants Beyond Locality and Classical
Decodability*, arXiv:2610.00502 (version held, sha256 ef050ec0…62605), §5.2, Theorem 5.30, p.29: "expected gate complexity"; proof, p.30: "at most four trials are
needed in expectation".

With `N` qubits and `c` classical bits, and each execution leaf of `T` weighted by its
probability, the expected charged work of one trial is `Σ_leaves Pr(leaf) · (work of leaf)`
(queries, gates, preparations, measurements and classical steps). The number of trials is
geometric with mean `1/acceptProb T`, so by Wald's identity the expected total cost of the restart
loop is
`(N + c + Σ_leaves Pr(leaf) · work(leaf)) / acceptProb T`.

**Formalization Note.** The space `N + c` is charged once per expected trial, which only
increases the cost. Statements require `acceptProb T > 0`. -/
noncomputable def expectedCost {N c k : ℕ}
    (T : AdaptiveMembershipProgram htcxGateSet (fun _ : Fin 0 => 0) (fun _ => false) N c (k + 1)) :
    ℝ :=
  ((N + c : ℕ) + ((adaptiveExecution (fun _ => 1) T (pureDensity (zeroKet N))
      (fun _ => false)).map fun leaf => leaf.1.2.trace.re * ((∑ j, leaf.2 j : ℕ) : ℝ)).sum) /
    acceptProb T

end TwoFoldOPI


