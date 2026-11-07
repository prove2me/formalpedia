-- Prove2me | Definitions.Def_TwoFoldOPI_restartSuccess
-- name    : TwoFoldOPI_restartSuccess
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T22:45:54.899652+00:00
-- url     : https://prove2.me/theorems/262489b8-5771-4abd-ad4b-42f9f9d68128
-- title:
--   Success probability of repeating a trial until it accepts
-- statement:
--   Repeating a trial program $T$ with fresh workspace until its flag is $1$, and outputting the answer of the accepting trial, succeeds (answer satisfies a predicate $\mathrm{good}$) with probability
--   $$\frac{\Pr[\text{flag}=1\ \wedge\ \mathrm{good}(\text{answer})]}{\Pr[\text{flag}=1]} .$$
--   This is the success probability of the restart algorithm of Theorem 5.30 ("On inequality, restart"), when the acceptance probability is positive; statements require that.
-- source:
--   Ragavan, Shutty, Quantum Algorithms for OPI Variants Beyond Locality and Classical Decodability, arXiv:2610.00502 (version held, sha256 ef050ec0…62605), §5.2, Theorem 5.30 and its proof, pp. 29–30

import Mathlib
import Definitions.Def_TwoFoldOPI_acceptProb

namespace TwoFoldOPI

open QAlgorithms QAlgorithms.OPI

/-- **Success of "repeat the trial until it accepts".**
Ragavan, Shutty, *Quantum Algorithms for OPI Variants Beyond Locality and Classical
Decodability*, arXiv:2610.00502 (version held, sha256 ef050ec0…62605), §5.2, Theorem 5.30 and its proof, pp.29–30 ("On inequality, restart").

Repeating the trial program `T` (fresh workspace each time) until its flag is `1` and outputting
that trial's answer succeeds with probability
`Pr[flag = 1 ∧ good(answer)] / Pr[flag = 1]`.

**Formalization Note.** This is the exact law of the restart loop when `acceptProb T > 0`
(statements require it). -/
noncomputable def restartSuccess {N c k : ℕ}
    (T : AdaptiveMembershipProgram htcxGateSet (fun _ : Fin 0 => 0) (fun _ => false) N c (k + 1))
    (good : (Fin k → Bool) → Prop) : ℝ :=
  membershipOutputLaw T (fun _ => 1)
      (fun o => ∃ bits, o = some bits ∧ bits (Fin.last k) = true ∧ good (bits ∘ Fin.castSucc)) /
    acceptProb T

end TwoFoldOPI


