-- Prove2me | Definitions.Def_MemQueryFeas_IsAdmissibleNoise
-- name    : MemQueryFeas_IsAdmissibleNoise
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:37:36.266098+00:00
-- url     : https://prove2.me/theorems/ca7f4d2f-bb35-46ff-9e7f-7e4459a649a2
-- title:
--   Admissible outcomes of NoiseAddition
-- statement:
--   Given $E_1,\dots,E_P$, a family of versions $E^{(i)}_{v',p}$ is **admissible** if every version is $\tilde d$-dimensional and lies within largest principal angle $\delta_p^{(i)}/\sqrt{3P}$ of its predecessor in Algorithm 1: $E^{(i+1)}_{v',p}$ for $i<N_p$, and $H_{v'}(E_p)$ for $i=N_p$. These are the possible outcomes of the skeleton construction for the given $E_1,\dots,E_P$.
-- source:
--   Yu–Blanchard, Exponential memory/query-complexity tradeoffs in high-accuracy feasibility problems, preprint (Nov. 3, 2026), Lemma 4, p.15 (PDF p.16); App. D.1, p.37

import Mathlib
import Definitions.Def_MemQueryFeas_thetaMax
import Definitions.Def_MemQueryFeas_IsOrthProj
import Definitions.Def_MemQueryFeas_imageProj
import Definitions.Def_MemQueryFeas_Hmap
import Definitions.Def_MemQueryFeas_IsPhase
import Definitions.Def_MemQueryFeas_Np
import Definitions.Def_MemQueryFeas_delta

namespace MemQueryFeas

/-- **Admissible outcomes of NoiseAddition.** Yu–Blanchard, *Exponential memory/query-complexity tradeoffs in high-accuracy feasibility problems*, preprint (Nov. 3, 2026), Lemma 4, p.15 (PDF p.16): "regardless of the
randomness used in NoiseAddition for sampling phases in each layer"; App. D.1, p.37: "the result
holds simultaneously for all admissible `δ_1, …, δ_P` and `U_1, …, U_P`". Algorithm 1 samples each
version in the ball `B(F^(i+1), δ^(i))`.

`IsAdmissibleNoise d ε P d̃ Eb c`: given base subspaces `Eb p = P_{E_p}`, the version values
`c p v' i` (`p ∈ [P]`, `v' ∈ V_{p−1}`, `0 ≤ i ≤ N_p`) are `d̃`-dimensional and each is within largest
principal angle `δ_p^(i)/√(3P)` of its predecessor in Algorithm 1: `c p v' (i+1)` for `i < N_p`, and
`H_{v'}(E_p)` for `i = N_p`. These are exactly the possible outputs of the skeleton construction
given `E_1, …, E_P`. -/
def IsAdmissibleNoise (d : ℕ) (ε : ℝ) (P dt : ℕ) (Eb : ℕ → Op d)
    (c : ℕ → List ℕ → ℕ → Op d) : Prop :=
  ∀ p, 1 ≤ p → p ≤ P → ∀ v', IsPhase (Np d ε P) (p - 1) v' → ∀ i ≤ Np d ε P p,
    IsOrthProj dt (c p v' i) ∧
      thetaMax (c p v' i)
          (if i = Np d ε P p then imageProj (Hmap (delta d ε P) c v') (Eb p) else c p v' (i + 1))
        ≤ delta d ε P p i / Real.sqrt (3 * P)

end MemQueryFeas


