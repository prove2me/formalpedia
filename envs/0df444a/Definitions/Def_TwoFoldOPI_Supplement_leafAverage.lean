-- Prove2me | Definitions.Def_TwoFoldOPI_Supplement_leafAverage
-- name    : TwoFoldOPI_Supplement_leafAverage
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T14:04:05.234826+00:00
-- url     : https://prove2.me/theorems/335550cb-dd6c-4379-b8bc-c3b816620f16
-- title:
--   The expected value of an operation count over one run of a program
-- statement:
--   A run of a program ends in branches, each with a probability and counts of queries, gates, resets, measurements and classical steps. This is the expectation $\sum_{\text{branch}}\Pr(\text{branch})\cdot\mathrm{cnt}(\text{branch})$ of a chosen count.
--
--   Divided by the acceptance probability of a trial, it is the expected count of the restart loop (Wald's identity), the "expected gate (query) complexity" of Theorem 5.28.
--
--   **Formalization Note** Same branch semantics as the published `QAlgorithms.OPI.membershipOutputLaw`.
-- source:
--   Ragavan, Shutty, Quantum Algorithms for OPI Variants Beyond Locality and Classical Decodability, arXiv:2610.00502 (version held, sha256 ef050ec0…62605), §5.2, Theorem 5.28 and its proof, pp. 27–28

import Mathlib
import Definitions.Def_QAlgorithms_Defs_OPIOraclePrograms

namespace TwoFoldOPI

namespace Supplement

open QAlgorithms QAlgorithms.OPI

/-- **The expected value of an operation count over one run of a program.**
Ragavan, Shutty, *Quantum Algorithms for OPI Variants Beyond Locality and Classical
Decodability*, arXiv:2610.00502 (version held, sha256 ef050ec0…62605), §5.2, Theorem 5.28, p.27: "expected gate complexity … and expected query complexity"; proof,
p.28: "The expected number of trials is at most 2/P_dec. Each trial costs T_dec + T_prep(q, M, τ) +
poly(M, log q, τ) gates and Q_dec + Q_prep(q, M, τ) queries".

A run of `P` from `|0^N⟩` with oracles `O` ends in leaves, each with a probability (the trace of
its subnormalized state) and a count vector (queries, gates, resets, measurements, classical steps,
in this order: `QAlgorithms.OPI.MembershipLeaf`). `leafAverage P O cnt = Σ_leaf Pr(leaf) ·
cnt(counts)`.

**Formalization Note.** Dividing by the acceptance probability of a trial gives the expected count of
"repeat until accept" (Wald's identity), as in the published `TwoFoldOPI.expectedCost`. -/
noncomputable def leafAverage {S : Set Gate} {r : ℕ} {a : Fin r → ℕ} {ctl : Fin r → Bool}
    {N c out : ℕ} (P : AdaptiveMembershipProgram S a ctl N c out)
    (O : (k : Fin r) → Matrix (Qubits (a k)) (Qubits (a k)) ℂ) (cnt : (Fin 5 → ℕ) → ℕ) : ℝ :=
  ((adaptiveExecution O P (pureDensity (zeroKet N)) (fun _ => false)).map fun leaf =>
    leaf.1.2.trace.re * (cnt leaf.2 : ℝ)).sum

end Supplement

end TwoFoldOPI


