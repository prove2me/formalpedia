-- Prove2me | Definitions.Def_PRUPermLayer_Supplement_mixAcceptProb
-- name    : PRUPermLayer_Supplement_mixAcceptProb
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T14:39:01.991938+00:00
-- url     : https://prove2.me/theorems/ad112983-9998-46e2-bf9d-99f5b585394d
-- title:
--   Acceptance probability $\langle A^{U,U^\dagger}|M|A^{U,U^\dagger}\rangle$ of a mixed-access algorithm
-- statement:
--   For a mixed-access algorithm with effect $M$ and oracle $U$, the probability of the output $1$ is
--   $$\Pr[A^{U,U^\dagger}=1]=\langle A^{U,U^\dagger}|\,M\,|A^{U,U^\dagger}\rangle,$$
--   where $|A^{U,U^\dagger}\rangle$ is the final state. For unitary $U$ this lies in $[0,1]$.
--
--   **Formalization Note** The real part of the inner product; for an effect the inner product is real.
-- source:
--   Shen–Zhong, Pseudorandom Unitaries from a Random Permutation and One Layer of Single-Qubit Gates, manuscript (STOC 2027 submission; held version sha256 395fcfa33ec861a7e9c10d88cfcefc2794b77ad1674c02661c9298c5ba565bcb), §2.2, p.9 (PDF p.11); Theorem 1.6, p.4 (PDF p.6)

import Mathlib
import Definitions.Def_PRUPermLayer_Supplement_mixFinalState

namespace PRUPermLayer.Supplement

/-- The acceptance probability `Pr[A^{U,U†} = 1] = ⟨ψ| M |ψ⟩` of a mixed-access algorithm with
oracle `U`, `ψ` its final state (Shen–Zhong, *Pseudorandom Unitaries from a Random Permutation and One Layer of Single-Qubit Gates*, manuscript (STOC 2027 submission; held version sha256 395fcfa3…5bcb), §2.2, p.9 (PDF p.11); Theorem 1.6, p.4 (PDF p.6)).

**Formalization Note** The real part of `⟨ψ, M ψ⟩`; for an effect `M` the inner product is real,
and for a unitary `U` the final state is a unit vector, so the value lies in `[0, 1]`. -/
noncomputable def mixAcceptProb {n q : ℕ} (alg : MixAlg n q)
    (U : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ) : ℝ :=
  (dotProduct (star (mixFinalState alg U)) (Matrix.mulVec alg.M (mixFinalState alg U))).re

end PRUPermLayer.Supplement


