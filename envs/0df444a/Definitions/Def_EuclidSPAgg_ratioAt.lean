-- Prove2me | Definitions.Def_EuclidSPAgg_ratioAt
-- name    : EuclidSPAgg_ratioAt
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:40:59.134097+00:00
-- url     : https://prove2.me/theorems/be5c00c2-96a4-49c2-bf7b-6526e8b9c5e5
-- title:
--   Ratio $\mathrm{SC}(x,f(x))/\mathrm{OPT}(x)$ at one profile
-- statement:
--   For a mechanism $f$ and a profile $x$, this is the quotient
--   $$
--   \frac{\mathrm{SC}(x,f(x))}{\mathrm{OPT}(x)}\in[0,\infty],
--   $$
--   with the paper's conventions: the quotient is $1$ if both costs vanish, and $+\infty$ if only the denominator vanishes.
--
--   **Formalization Note** The value lies in the extended nonnegative reals. The two conventions are written out by cases; extended-real division is not used, because it would give $0/0=0$ rather than $1$.
-- source:
--   Jia, Strategyproof Aggregation in Euclidean Spaces: Rigidity and Median Optimality, arXiv:2609.19394 (held version, sha256 891e6125…), Section 2.1, p.9 (PDF p.11)

import Mathlib
import Definitions.Def_EuclidSPAgg_Mech
import Definitions.Def_EuclidSPAgg_OPT
open RBMSensitivity (E)

namespace EuclidSPAgg

/-- The ratio `SC(x, f(x)) / OPT(x)` at one profile, with the paper's conventions (Jia, *Strategyproof Aggregation in Euclidean Spaces: Rigidity and Median Optimality*, arXiv:2609.19394 (held version, sha256 891e6125…),
Section 2.1, p.9 (PDF p.11)): the quotient is one if both costs vanish and infinite if only the
denominator vanishes.

**Formalization Note** Valued in `ℝ≥0∞`. The conventions `0/0 = 1` and `c/0 = ∞` (`c > 0`) are
written out with `if`; `ENNReal` division is not used, since it has `0/0 = 0`. -/
noncomputable def ratioAt {n d : ℕ} (f : Mech n d) (x : Fin n → E d) : ENNReal :=
  if OPT x = 0 then (if SC x (f x) = 0 then 1 else ⊤)
  else ENNReal.ofReal (SC x (f x) / OPT x)

end EuclidSPAgg


