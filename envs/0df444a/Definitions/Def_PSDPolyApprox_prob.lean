-- Prove2me | Definitions.Def_PSDPolyApprox_prob
-- name    : PSDPolyApprox_prob
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T07:49:53.702983+00:00
-- url     : https://prove2.me/theorems/5996d7be-16bd-4d68-84d8-1ff8093c123a
-- title:
--   The uniform probability measure $\mu$ on $H_n$
-- statement:
--   The uniform probability measure on the hypercube: for $S\subseteq H_n$,
--   $$
--   \mu(S)=\frac{|S|}{2^n}.
--   $$
--   It is a probability, not a count.
-- source:
--   Fawzi, On polyhedral approximations of the positive semidefinite cone, arXiv:1811.09649v1, §2.1, p.3

import Mathlib
import Definitions.Def_PSDPolyApprox_Cube

namespace PSDPolyApprox

/-- **The uniform probability measure `µ` on the hypercube.**
Fawzi, arXiv:1811.09649v1, §2.1, p.3: "let µ be the uniform probability measure on Hn".

`prob s = µ(s) = |s| / 2ⁿ` for a set `s ⊆ Hₙ` (a probability, not a count). -/
noncomputable def prob {n : ℕ} (s : Set (Cube n)) : ℝ :=
  (s.ncard : ℝ) / (2 : ℝ) ^ n

end PSDPolyApprox


