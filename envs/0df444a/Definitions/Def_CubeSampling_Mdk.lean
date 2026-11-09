-- Prove2me | Definitions.Def_CubeSampling_Mdk
-- name    : CubeSampling_Mdk
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T12:14:08.907871+00:00
-- url     : https://prove2.me/theorems/c68da8a8-6d42-423b-a47c-147a6a39a36b
-- title:
--   $M_{d,k} = \binom{d}{\lfloor k^{1/3}\rfloor}$
-- statement:
--   $$
--   M_{d,k} = \binom{d}{\lfloor k^{1/3} \rfloor}.
--   $$
--   It is the dimension of the concentrated subspace built in the subspace uncertainty principle, and the range of model dimensions $m$ for which the two-sided threshold bound is proved.
--
--   **Formalization Note** $k^{1/3}$ is the real power of $k$ and $\lfloor\cdot\rfloor$ the natural-number floor.
-- source:
--   Weinberger, Subspace Uncertainty and Sharp Sampling Thresholds on the Boolean Cube, arXiv:2610.12358 (version of 2 Nov 2026), Section 1.1, p.4

import Mathlib

namespace CubeSampling

/-- `M_{d,k} = C(d, ⌊k^{1/3}⌋)` (Weinberger, *Subspace Uncertainty and Sharp Sampling Thresholds on the Boolean Cube*, arXiv:2610.12358 (version of 2 Nov 2026, sha256 43fdcd90…4f79), §1.1, p.4).

**Formalization Note** `k^{1/3}` is the real power `(k : ℝ) ^ (1/3 : ℝ)` and `⌊·⌋` is `Nat.floor`. -/
noncomputable def Mdk (d k : ℕ) : ℕ := d.choose ⌊(k : ℝ) ^ ((1 : ℝ) / 3)⌋₊

end CubeSampling


