-- Prove2me | Definitions.Def_LineVsPoint_sec3D
-- name    : LineVsPoint_sec3D
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T08:03:06.07834+00:00
-- url     : https://prove2.me/theorems/e116ba17-625c-4e7b-a2f5-4e3decaa0109
-- title:
--   The Section 3 parameters $D=\lceil 4(dq^2)^{1/3}\rceil$ and $k=\lfloor \varepsilon q/1000\rfloor$
-- statement:
--   In the bivariate case the paper fixes the interpolation degree and the pruning threshold
--
--   $$
--   D=\bigl\lceil 4(dq^2)^{1/3}\bigr\rceil,\qquad k=\Bigl\lfloor \frac{\varepsilon q}{1000}\Bigr\rfloor ,
--   $$
--
--   where $q$ is the field size, $d$ the degree of the line table and $\varepsilon$ a lower bound on the acceptance probability. $D$ does not depend on $\varepsilon$; it is the weighted degree of the interpolant $A$, and it is what sets the cube-root threshold.
--
--   **Formalization Note** `sec3D d q` and `sec3k ε q` use `Nat.ceil` and `Nat.floor` of real numbers, with the real exponent $1/3$.
-- source:
--   Dao, Kominers, Thaler, Zheng, Cube-Root Soundness Is Optimal for the Line–versus–Point Test (manuscript, sha256 328a8943…), §3, p.15

import Mathlib

set_option autoImplicit false

namespace LineVsPoint

/-- The **interpolation degree** of Section 3: Dao, Kominers, Thaler, Zheng, *Cube-Root
Soundness Is Optimal for the Line–versus–Point Test* (manuscript, sha256 328a8943…), §3, p.15:
"Let `D = ⌈4(dq²)^{1/3}⌉`".

**Formalization Note.** `⌈·⌉` is `Nat.ceil` of a real number, and the exponent `1/3` is the real
number `(1/3 : ℝ)` (`Real.rpow`). -/
noncomputable def sec3D (d q : ℕ) : ℕ :=
  ⌈4 * ((d : ℝ) * (q : ℝ) ^ 2) ^ (1 / 3 : ℝ)⌉₊

/-- The **pruning threshold** of Section 3: manuscript (sha256 328a8943…), §3, p.15:
"`k = ⌊εq/1000⌋`".

**Formalization Note.** `⌊·⌋` is `Nat.floor` of a real number. -/
noncomputable def sec3k (ε : ℝ) (q : ℕ) : ℕ :=
  ⌊ε * (q : ℝ) / 1000⌋₊

end LineVsPoint


