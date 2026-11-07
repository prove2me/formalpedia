-- Prove2me | Definitions.Def_TwoFoldOPI_acceptProb
-- name    : TwoFoldOPI_acceptProb
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T22:44:27.060532+00:00
-- url     : https://prove2.me/theorems/31b68402-2024-4769-84ce-3a73d596b9f0
-- title:
--   Acceptance probability of a trial program
-- statement:
--   A **trial program** is an oracle-free adaptive program over $\{H,T,\mathrm{CNOT}\}$ whose output has $k+1$ bits: the last bit is an acceptance flag and the first $k$ bits are the answer. Its acceptance probability is
--   $$\Pr[\text{the program halts with flag } 1].$$
--   In the proof of Theorem 5.30, a trial accepts when the decoded word equals the retained codeword; otherwise the algorithm restarts.
-- source:
--   Ragavan, Shutty, Quantum Algorithms for OPI Variants Beyond Locality and Classical Decodability, arXiv:2610.00502 (version held, sha256 ef050ec0…62605), §5.2, proof of Theorem 5.30, p. 30

import Mathlib
import Definitions.Def_QAlgorithms_Defs_OPIOraclePrograms
import Definitions.Def_QAlgorithms_Defs_GradientMethods

namespace TwoFoldOPI

open QAlgorithms QAlgorithms.OPI

/-- **The acceptance probability of one trial.**
Ragavan, Shutty, *Quantum Algorithms for OPI Variants Beyond Locality and Classical
Decodability*, arXiv:2610.00502 (version held, sha256 ef050ec0…62605), §5.2, proof of Theorem 5.30, p.30: "Measure only whether its decoded-word register equals
the retained register. On inequality, restart; equality occurs with probability p."

A *trial program* is an oracle-free program over `{H, T, CNOT}` whose output is `k + 1` bits: the
last bit is the acceptance flag, the first `k` bits are the answer. `acceptProb T` is the
probability that `T` halts with flag `1`.

**Formalization Note.** The oracle argument of `membershipOutputLaw` ranges over `Fin 0` and is
never called. -/
noncomputable def acceptProb {N c k : ℕ}
    (T : AdaptiveMembershipProgram htcxGateSet (fun _ : Fin 0 => 0) (fun _ => false) N c (k + 1)) :
    ℝ :=
  membershipOutputLaw T (fun _ => 1) fun o => ∃ bits, o = some bits ∧ bits (Fin.last k) = true

end TwoFoldOPI


