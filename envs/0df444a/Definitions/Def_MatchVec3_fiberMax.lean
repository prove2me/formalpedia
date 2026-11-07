-- Prove2me | Definitions.Def_MatchVec3_fiberMax
-- name    : MatchVec3_fiberMax
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T10:41:28.423066+00:00
-- url     : https://prove2.me/theorems/7bd99e65-b5b2-483e-8465-6ec6a295ca19
-- title:
--   $M_L(U)$: the largest $L$-sum fiber
-- statement:
--   The **largest $L$-sum fiber** of $U$ is
--
--   $$M_L(U)=\max_x\ \#\Big\{A\in\binom{[K]}{L}:\ \Sigma_L(A)=x\Big\}.$$
--
--   It is the largest number of $L$-subsets that produce the same sum, and it controls the largest atom of the random sum $S_L^*(U)$.
--
--   **Formalization Note** The maximum runs over the attained sums, which gives the same value as a maximum over all $x$, since a sum that is not attained has an empty fiber. The value is $0$ when $K<L$.
-- source:
--   Aggarwal, Obremski, Subexponential Upper Bounds for 3-Restricted Matching Vector Families, STOC 2027 submission (manuscript sha256 44199413…), §3, p.10, and §5, p.13

import Mathlib
import Definitions.Def_MatchVec3_fiber

namespace MatchVec3

/-- **The largest `L`-sum fiber** `M_L(U) = max_x #{A ∈ ([K] choose L) : Σ_L(A) = x}` (Aggarwal,
Obremski, STOC 2027 submission (manuscript sha256 44199413…), §3, p.10, and §5, p.13).

**Formalization Note** The maximum runs over the attained sums `x = Σ_L(A)`, which gives the same
value as a maximum over all `x`, since a sum that is not attained has an empty fiber; this form needs
no `Fintype (ZMod m)`. The value is `0` when `K < L`, in which case every fiber is empty. -/
def fiberMax {m n K : ℕ} (U : Fin K → Fin n → ZMod m) (L : ℕ) : ℕ :=
  (Finset.powersetCard L (Finset.univ : Finset (Fin K))).sup fun A =>
    (fiber U L (∑ i ∈ A, U i)).card

end MatchVec3


