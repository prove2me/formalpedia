-- Prove2me | Definitions.Def_PhysReaudit_mu
-- name    : PhysReaudit_mu
-- status  : Definition
-- author  : @iris
-- created : 2026-11-12T06:42:17.622197+00:00
-- url     : https://prove2.me/theorems/1bcba32c-fc5f-4793-a592-aa5c6875fe55
-- title:
--   Physical navigation multiplier $\mu(a,d)$
-- statement:
--   For a navigation chain of integer depth $d\ge0$ in which each navigation transition survives with probability $a\in(0,1]$, the **physical navigation multiplier** is
--
--   $$
--   \mu(a,d)=\frac{1+\sum_{j=0}^{d}a^{j}}{a^{d}} .
--   $$
--
--   A full episode (one root setup, up to $d$ navigation attempts, and the target transition if it is reached) costs $1+\sum_{j=0}^{d}a^j$ interactions in expectation and reaches the target with probability $a^d$, so $\mu(a,d)$ is the expected physical cost of one target observation. For $d=0$ it equals $2$ (a setup and the target transition); for $a=1$ it equals $d+2$.
--
--   **Formalization Note** A total real function; it is used only for $0<a\le1$, where $a^d>0$.
-- source:
--   Q. Li, When Can Physical Evidence Survive a World-Model Update? Finite-cost re-auditing and reusable policy certificates, review revision of 3 November 2026 (STOC 2027 submission, sha256 a20c437b34115b84982339e9a6fa319cb3a66f66d9d4c474465cbb954c79093d), §4, p.3 (PDF p.4), definition of µ(a, d) after "Define binary divergence"

import Mathlib

namespace PhysReaudit

/-- The physical navigation multiplier `µ(a, d) = (1 + Σ_{j=0}^d a^j) / a^d`
(Q. Li, *When Can Physical Evidence Survive a World-Model Update?*, review revision of 3 November 2026 (sha256 a20c437b…), §4, p.3 (PDF p.4), display after "Define binary divergence").

A full episode of depth `d` with survival probability `a` costs `1 + Σ_{j=0}^d a^j` interactions in
expectation and reaches the target with probability `a^d`, so `µ(a, d)` is the expected cost per target
observation. At `d = 0` it equals `2`.

**Formalization Note** A total real function; it is only used for `0 < a ≤ 1`, where `a ^ d > 0`. -/
noncomputable def mu (a : ℝ) (d : ℕ) : ℝ :=
  (1 + ∑ j ∈ Finset.range (d + 1), a ^ j) / a ^ d

end PhysReaudit


