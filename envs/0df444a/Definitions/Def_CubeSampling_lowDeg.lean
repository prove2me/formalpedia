-- Prove2me | Definitions.Def_CubeSampling_lowDeg
-- name    : CubeSampling_lowDeg
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T12:17:11.55564+00:00
-- url     : https://prove2.me/theorems/646b5596-d758-4108-b055-fbf169acae6f
-- title:
--   The space $P_{d,k}$ of functions of degree at most $k$
-- statement:
--   The space of real functions on $\{-1,1\}^d$ of **degree at most $k$** is
--   $$
--   P_{d,k} = \operatorname{span}\{\chi_S : S \subseteq [d],\ |S| \le k\},
--   $$
--   a real vector space of dimension $D_{d,k}$.
-- source:
--   Weinberger, Subspace Uncertainty and Sharp Sampling Thresholds on the Boolean Cube, arXiv:2610.12358 (version of 2 Nov 2026), Section 1.1, p.3

import Mathlib
import Definitions.Def_CubeSampling_walsh

namespace CubeSampling

/-- The space `P_{d,k} = span{χ_S : |S| ≤ k}` of real functions on `{−1, 1}^d` of degree at most
`k` (Weinberger, *Subspace Uncertainty and Sharp Sampling Thresholds on the Boolean Cube*, arXiv:2610.12358 (version of 2 Nov 2026, sha256 43fdcd90…4f79), §1.1, p.3). -/
noncomputable def lowDeg (d k : ℕ) : Submodule ℝ (Cube d → ℝ) :=
  Submodule.span ℝ {f | ∃ S : Finset (Fin d), S.card ≤ k ∧ walsh S = f}

end CubeSampling


