-- Prove2me | Definitions.Def_CubeSampling_Irate
-- name    : CubeSampling_Irate
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T12:14:29.354149+00:00
-- url     : https://prove2.me/theorems/80faf0d5-835c-4934-b98e-ef293e64dd65
-- title:
--   Binomial rate $I(z) = \log 2 - H_2((1-z)/2)$
-- statement:
--   $$
--   I(z) = \log 2 - H_2\Bigl(\frac{1-z}{2}\Bigr), \qquad 0 \le z < 1,
--   $$
--   the Chernoff rate of the binomial tail: $\mu_D(S_D \ge u) \le \exp\{-D\,I(u/D)\}$.
-- source:
--   Weinberger, Subspace Uncertainty and Sharp Sampling Thresholds on the Boolean Cube, arXiv:2610.12358 (version of 2 Nov 2026), proof of Lemma 4.3, p.18; Section 5.1, p.20

import Mathlib

namespace CubeSampling

/-- The binomial rate `I(z) = log 2 − H₂((1 − z)/2)` (Weinberger, *Subspace Uncertainty and Sharp Sampling Thresholds on the Boolean Cube*, arXiv:2610.12358 (version of 2 Nov 2026, sha256 43fdcd90…4f79), proof of Lemma 4.3, p.18 and §5.1, p.20). -/
noncomputable def Irate (z : ℝ) : ℝ := Real.log 2 - Real.binEntropy ((1 - z) / 2)

end CubeSampling


