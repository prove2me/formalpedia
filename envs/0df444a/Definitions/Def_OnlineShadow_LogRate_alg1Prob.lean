-- Prove2me | Definitions.Def_OnlineShadow_LogRate_alg1Prob
-- name    : OnlineShadow_LogRate_alg1Prob
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T04:15:41.459213+00:00
-- url     : https://prove2.me/theorems/330676b2-ee42-4b06-b530-ed318631c53a
-- title:
--   Probability of an outcome string of Algorithm 1
-- statement:
--   For an outcome string $\omega$ of Algorithm 1 run on $n$ copies of the state $\rho$, its probability is
--   $$\Pr(\omega)=\mathrm{Tr}\big(K_\omega\,\rho^{\otimes n}K_\omega^\dagger\big),$$
--   where $K_\omega$ is the product of the Kraus operators of the soft binary measurements performed on $\omega$ (and $0$ if $\omega$ flags at a coordinate the run does not use). These probabilities sum to $1$ over all strings, and the probability of an event of the run is the sum over the strings in it.
-- source:
--   Chen, O'Donnell, Pelecanos, Wright, Online Shadow Tomography Matching the Classical Bounds, STOC 2027 submission (manuscript of November 2, 2026, sha256 90993723…dc3a9), Algorithm 1, p. 11; §4.2, p. 12

import Mathlib
import Definitions.Def_ShadowTomography_UpperBound_tensorPow
import Definitions.Def_OnlineShadow_LogRate_alg1Run

open scoped Matrix

namespace OnlineShadow.LogRate

/-- The probability of the outcome string `ω` in a run of Algorithm 1 on `ρ^{⊗n}`
(Chen, O'Donnell, Pelecanos, Wright, *Online Shadow Tomography Matching the Classical Bounds*, STOC 2027
submission (manuscript of November 2, 2026, sha256 90993723…dc3a9), Algorithm 1, p.11, and §4.2,
p.12): `Tr(K_ω ρ^{⊗n} K_ωᴴ)` with `K_ω = alg1Kraus … ω`. -/
noncomputable def alg1Prob {d : ℕ} (n m K : ℕ) (ε lam : ℝ) (adv : Adversary d)
    (ρ : Matrix (Fin d) (Fin d) ℂ) (ω : Fin (2 * (m + K)) → Bool) : ℝ :=
  (alg1Kraus n m K ε lam adv ω * ShadowTomography.UpperBound.tensorPow ρ n *
    (alg1Kraus n m K ε lam adv ω)ᴴ).trace.re

end OnlineShadow.LogRate


