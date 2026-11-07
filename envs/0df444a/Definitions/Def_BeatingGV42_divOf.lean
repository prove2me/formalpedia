-- Prove2me | Definitions.Def_BeatingGV42_divOf
-- name    : BeatingGV42_divOf
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:31:57.537747+00:00
-- url     : https://prove2.me/theorems/ea8bb8cb-c24a-4966-bae3-d421ebecb3c1
-- title:
--   The principal divisor $(f)$
-- statement:
--   For $f\in F^\times$, the **principal divisor** of $f$ is $(f)=\sum_P\nu_P(f)\,P$, where $\nu_P$ is the normalized valuation at the place $P$; it has degree $0$. It appears in the map $\Phi(f,\gamma)=(f)+G_\gamma-\sum_{i\notin S}P_i$ of Claim 4.4.
--
--   **Formalization Note** The platform's `HasPrincipalDivisors k F` (part of `IsCurveOver`) provides, for each $f\ne 0$, a finitely supported divisor with values $\nu_P(f)$; it is unique, and `divOf f` is that divisor. For $f=0$ the value is the junk $0$, never used.
-- source:
--   Cohen, Manket, Beating the Gilbert–Varshamov Bound at Alphabet Size 42, manuscript of October 24, 2026 (STOC 2027 submission; held version sha256 da05fc8e…eb595), §3, p.11 (PDF p.13)

import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve

namespace BeatingGV42

open Classical in
/-- **The principal divisor** `(f) = Σ_P ν_P(f) P` of `f ∈ F^×` (Cohen, Manket, *Beating the Gilbert–Varshamov Bound at Alphabet Size 42*, manuscript of October 24, 2026 (held version sha256 da05fc8e…), §3, p.11 (PDF p.13)).

**Formalization Note** Under the platform's `HasPrincipalDivisors k F` (part of `IsCurveOver`)
every nonzero `f` has a finitely supported divisor `D` with `D v = v.ord f` for all places `v`;
a finitely supported function is determined by its values, so the chosen `D` is unique and is `(f)`.
For `f = 0` the value is the junk `0`; the paper's `(f)` is only used for `f ≠ 0`. -/
noncomputable def divOf {k F : Type*} [Field k] [Field F] [Algebra k F] [HasPrincipalDivisors k F]
    (f : F) : Divisor k F :=
  if hf : f = 0 then 0 else Classical.choose (HasPrincipalDivisors.exists_divisor (K := k) f hf)

end BeatingGV42


