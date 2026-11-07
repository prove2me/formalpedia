-- Prove2me | Definitions.Def_NSWBetter_ST
-- name    : NSWBetter_ST
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:53:21.48554+00:00
-- url     : https://prove2.me/theorems/7173d7d7-f018-4ceb-8804-c529401ea17c
-- title:
--   $\mathrm{ST}(x)$: expected log Nash welfare after ST rounding
-- statement:
--   $\mathrm{ST}(x)=\frac1n\sum_{i\in N}\mathbb E[\ln v_i(X_i)]$, the expected log Nash welfare of the allocation produced by ST rounding of $x$ with scheme $D$.
-- source:
--   Viswanathan, A Better-than-e^{1/e} Approximation Algorithm for Nash Social Welfare under Additive Valuations, arXiv:2607.13340 (held version, sha256 08811cb468c2df39231dca4222c5af94163587c7c83e205e50bbf0b91fc1deb3), Section 4, p.17 (definition of ST(x))

import Mathlib
import Definitions.Def_NSWBetter_STi

namespace NSWBetter

/-- **Expected log Nash welfare under ST rounding.**
Viswanathan, *A Better-than-e^{1/e} Approximation Algorithm for Nash Social Welfare under Additive Valuations*, arXiv:2607.13340 (held version, sha256 08811cb4…), Section 4, p.17: "We also define ST(x) = (1/n) Σ_(i∈N) E[ln(vi(Xi))]". -/
noncomputable def ST {n m : ℕ} (v : Fin n → Fin m → ℝ) (D : Finset (Fin n × Fin m × Fin m) → ℝ) :
    EReal :=
  ((1 / n : ℝ) : EReal) * ∑ i, STi v D i

end NSWBetter


