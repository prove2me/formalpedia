-- Prove2me | Definitions.Def_CubeSampling_IsHarmonic
-- name    : CubeSampling_IsHarmonic
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T12:17:09.947654+00:00
-- url     : https://prove2.me/theorems/5e9caa01-e34c-4c71-a503-263bbe170a8f
-- title:
--   Harmonic polynomials $H_{d,r}$
-- statement:
--   $H_{d,r}$ is the space of **homogeneous multilinear degree-$r$ harmonic polynomials** on $\{-1,1\}^d$: functions $f \in \operatorname{span}\{\chi_S : |S| = r\}$ with
--   $$
--   \sum_{i=1}^d \partial_i f = 0 .
--   $$
--   For example $H_{d,0}$ consists of the constants and $H_{d,1} = \{\sum_i v_i x_i : \sum_i v_i = 0\}$.
-- source:
--   Weinberger, Subspace Uncertainty and Sharp Sampling Thresholds on the Boolean Cube, arXiv:2610.12358 (version of 2 Nov 2026), Section 5, p.19

import Mathlib
import Definitions.Def_CubeSampling_walsh
import Definitions.Def_CubeSampling_cubeDeriv

namespace CubeSampling

/-- `f ∈ H_{d,r}`, the homogeneous multilinear degree-`r` harmonic polynomials (Weinberger, *Subspace Uncertainty and Sharp Sampling Thresholds on the Boolean Cube*, arXiv:2610.12358 (version of 2 Nov 2026, sha256 43fdcd90…4f79), §5, p.19):
`f ∈ span{χ_S : |S| = r}` and `∑_{i=1}^d ∂_i f = 0`. -/
def IsHarmonic (d r : ℕ) (f : Cube d → ℝ) : Prop :=
  f ∈ Submodule.span ℝ {g | ∃ S : Finset (Fin d), S.card = r ∧ walsh S = g} ∧
    ∑ i, cubeDeriv i f = 0

end CubeSampling


