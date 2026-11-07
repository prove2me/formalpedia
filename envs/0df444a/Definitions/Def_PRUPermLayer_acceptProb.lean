-- Prove2me | Definitions.Def_PRUPermLayer_acceptProb
-- name    : PRUPermLayer_acceptProb
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T07:28:06.93877+00:00
-- url     : https://prove2.me/theorems/58a99e72-09eb-4d3d-a17d-61b994c134ec
-- title:
--   Acceptance probability $\Pr[A^U = 1] = \langle A^U | M | A^U\rangle$
-- statement:
--   The **acceptance probability** of a forward algorithm with final effect $M$ and oracle $U$ is
--   $$
--   \Pr[A^U = 1] = \langle A^U | M | A^U \rangle ,
--   $$
--   the probability that the final two-outcome measurement $\{M, I - M\}$ gives the outcome $1$.
--
--   **Formalization Note** The real part of the inner product is taken; for an effect it is real, and for unitary $U$ it lies in $[0,1]$ (checked in the sanity file).
-- source:
--   Shen–Zhong, Pseudorandom Unitaries from a Random Permutation and One Layer of Single-Qubit Gates, manuscript (STOC 2027 submission; held version sha256 395fcfa3…5bcb), §2.2, p.9 (PDF p.11)

import Mathlib
import Definitions.Def_PRUPermLayer_finalState

namespace PRUPermLayer

/-- The acceptance probability `Pr[A^U = 1] = ⟨A^U| M |A^U⟩` of a forward algorithm with oracle
`U` (Shen–Zhong, *Pseudorandom Unitaries from a Random Permutation and One Layer of Single-Qubit Gates*, manuscript (STOC 2027 submission; held version sha256 395fcfa3…5bcb), §2.2, p.9 (PDF p.11)).

**Formalization Note** The real part of `⟨ψ, M ψ⟩`; for an effect `M` the inner product is real,
and for a unitary `U` it lies in `[0, 1]` (checked in the sanity file). -/
noncomputable def acceptProb {n t : ℕ} (alg : FwdAlg n t) (U : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ) :
    ℝ :=
  (dotProduct (star (finalState alg U)) (Matrix.mulVec alg.M (finalState alg U))).re

end PRUPermLayer


