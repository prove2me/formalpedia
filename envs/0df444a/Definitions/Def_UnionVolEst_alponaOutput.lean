-- Prove2me | Definitions.Def_UnionVolEst_alponaOutput
-- name    : UnionVolEst_alponaOutput
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T08:03:46.839211+00:00
-- url     : https://prove2.me/theorems/bbe88f7d-063f-41ae-939a-f35fd0c1f3d0
-- title:
--   Output $|X|/p$ of a run (line 16)
-- statement:
--   The output of a terminated run with final multiset $X$ and intensity $p$ is
--   $$
--   \mathrm{Out} = \frac{|X|}{p}.
--   $$
--
--   **Formalization Note** A run that never terminates (a null event) outputs $0$, which lies outside $[(1-\varepsilon)F_0,(1+\varepsilon)F_0]$ when $F_0>0$, so it is counted as a failure.
-- source:
--   Banerjee, Bal, Basu, Chakraborty, Chanda, Sarkar, Estimating the Volume of a Union of Convex Bodies, arXiv:2611.06364 (held version, sha256 15de4f2e…26bd24), §4.3, Algorithm 1 line 16, p.15 (PDF p.17)

import Mathlib
import Definitions.Def_UnionVolEst_AlponaState

namespace UnionVolEst

/-- The output of Algorithm 1, line 16 (Banerjee–Bal–Basu–Chakraborty–Chanda–Sarkar, *Estimating the Volume of a Union of Convex Bodies*, arXiv:2611.06364 (held version, sha256 15de4f2e…26bd24), §4.3, printed p.15, PDF p.17): `|X|/p`
`= |X| · 2^{level}` for a terminated run.

**Formalization Note** On a run that never terminates (`none`, a null event) the output is `0`,
which lies outside `(1 ± ε)F₀` for every `ε < 1` and union of positive volume, so it is counted as
a failure. -/
noncomputable def alponaOutput {n : ℕ} : Option (AlponaState n) → ℝ
  | some s => (s.X.length : ℝ) * 2 ^ s.level
  | none => 0

end UnionVolEst


