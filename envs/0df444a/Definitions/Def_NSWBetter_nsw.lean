-- Prove2me | Definitions.Def_NSWBetter_nsw
-- name    : NSWBetter_nsw
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:52:09.0513+00:00
-- url     : https://prove2.me/theorems/e2dfed30-b4ea-471c-a818-0653c3b7a856
-- title:
--   Nash social welfare $\mathrm{NSW}(X)=(\prod_i v_i(X_i))^{1/n}$
-- statement:
--   The **Nash social welfare** of an allocation $X$ is the geometric mean of the agents' utilities,
--   $$\mathrm{NSW}(X)=\Bigl(\prod_{i\in N}v_i(X_i)\Bigr)^{1/n}.$$
--
--   It is the objective maximized in Theorem 1.1; $\mathrm{NSW}(I)$ denotes its maximum over allocations.
--
--   **Formalization Note** The root is `Real.rpow`; for nonnegative valuations the product is nonnegative. With $n=0$ the value is $1$.
-- source:
--   Viswanathan, A Better-than-e^{1/e} Approximation Algorithm for Nash Social Welfare under Additive Valuations, arXiv:2607.13340 (held version, sha256 08811cb468c2df39231dca4222c5af94163587c7c83e205e50bbf0b91fc1deb3), Section 2, p.9 (definition of NSW(X))

import Mathlib
import Definitions.Def_NSWBetter_Inst
import Definitions.Def_NSWBetter_Alloc
import Definitions.Def_NSWBetter_util

namespace NSWBetter

/-- **Nash social welfare of an allocation.**
Viswanathan, *A Better-than-e^{1/e} Approximation Algorithm for Nash Social Welfare under Additive Valuations*, arXiv:2607.13340 (held version, sha256 08811cb4…), Section 2, p.9: "The Nash social welfare … of an allocation X (denoted NSW(X)) is defined as the geometric mean of agent utilities; formally, NSW(X) = (Π_(i∈N) vi(Xi))^(1/n)."

`nsw I X = (Π_i v_i(X_i))^(1/n)`, with `Real.rpow`.

**Formalization Note.** On well-formed instances the product is `≥ 0`, so `rpow` is the usual root. For `n = 0` the empty product is `1` and the value is `1`. -/
noncomputable def nsw (I : Inst) (X : Alloc I) : ℝ :=
  (∏ i, util I X i) ^ ((1 : ℝ) / I.n)

end NSWBetter


