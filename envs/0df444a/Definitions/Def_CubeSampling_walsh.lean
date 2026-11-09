-- Prove2me | Definitions.Def_CubeSampling_walsh
-- name    : CubeSampling_walsh
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T12:16:09.316064+00:00
-- url     : https://prove2.me/theorems/a7960783-0cdf-487d-9f51-61083599beb4
-- title:
--   Walsh character $\chi_S(x) = \prod_{i\in S} x_i$
-- statement:
--   For $S \subseteq [d] = \{1,\dots,d\}$, the **Walsh character** is
--   $$
--   \chi_S(x) = \prod_{i \in S} x_i, \qquad x \in \{-1,1\}^d,
--   $$
--   with $\chi_\emptyset = 1$. The $2^d$ characters form an orthonormal basis of the functions on the cube.
-- source:
--   Weinberger, Subspace Uncertainty and Sharp Sampling Thresholds on the Boolean Cube, arXiv:2610.12358 (version of 2 Nov 2026), Section 1.1, p.3

import Mathlib
import Definitions.Def_CubeSampling_coord

namespace CubeSampling

/-- The Walsh character `χ_S(x) = ∏_{i ∈ S} x_i` for `S ⊆ [d]` (Weinberger, *Subspace Uncertainty and Sharp Sampling Thresholds on the Boolean Cube*, arXiv:2610.12358 (version of 2 Nov 2026, sha256 43fdcd90…4f79), §1.1, p.3). `χ_∅ = 1`. -/
def walsh {d : ℕ} (S : Finset (Fin d)) (x : Cube d) : ℝ := ∏ i ∈ S, coord x i

end CubeSampling


