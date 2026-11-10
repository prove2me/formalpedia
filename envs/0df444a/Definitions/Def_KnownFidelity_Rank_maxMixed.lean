-- Prove2me | Definitions.Def_KnownFidelity_Rank_maxMixed
-- name    : KnownFidelity_Rank_maxMixed
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T21:45:47.432444+00:00
-- url     : https://prove2.me/theorems/2b35f7dc-f7b3-45b1-be69-cba96bfb78b0
-- title:
--   The maximally mixed state $I_q/q$ on $\mathbb C^q$
-- statement:
--   The maximally mixed state on $\mathbb C^q$ is $I_q/q$. It is the reference for which Theorem 1.2's lower bound holds and for which Proposition 4.1 builds hard instances.
--
--   **Formalization Note** At $q=0$ the matrix is empty.
-- source:
--   Lee, Jo, Fidelity Estimation to a Known Quantum State Is Nearly Quadratic in the Smaller Rank, arXiv:2608.01770, Theorem 1.2, p. 2 (PDF p. 4)

import Mathlib

namespace KnownFidelity.Rank

/-- **The maximally mixed state `I_q/q` on `ℂ^q`.**
Lee, Jo, *Fidelity Estimation to a Known Quantum State Is Nearly Quadratic in the Smaller Rank*,
arXiv:2608.01770, Theorem 1.2, printed p. 2 (PDF p. 4): "The lower bound holds for the reference
I_q/q and unknown states supported on C^q."

**Formalization Note.** `(q : ℂ)⁻¹ • 1` on `Fin q`; at `q = 0` the matrix is empty. -/
noncomputable def maxMixed (q : ℕ) : Matrix (Fin q) (Fin q) ℂ :=
  (q : ℂ)⁻¹ • (1 : Matrix (Fin q) (Fin q) ℂ)

end KnownFidelity.Rank


