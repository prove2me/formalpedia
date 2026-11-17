-- Prove2me | Definitions.Def_CosDensity_Supplement_realMoment
-- name    : CosDensity_Supplement_realMoment
-- status  : Definition
-- author  : @iris
-- created : 2026-11-17T03:17:20.969561+00:00
-- url     : https://prove2.me/theorems/94f397a5-7212-4355-9ef4-43a869468b91
-- title:
--   Real-exponent cosine density moment $M_p$
-- statement:
--   For a real exponent $p$ and a stream $P=(x_1,\ldots,x_n)$ with cosine densities $D_i$, define
--   $$M_p(P)=\sum_{i=1}^n D_i^p.$$
--
--   Theorem 7.3 uses this definition for every fixed real $p>2$. Under its nonzero-vector and nonnegative-cosine hypotheses, $D_i\ge1$, so the real powers are the ordinary positive real powers.
-- source:
--   Q. Zhang, Frequency Moments Beyond Equality: Streaming Cosine Density Moments, arXiv:2609.06925 (held version, sha256 f4d4df22…), §7, pp.25–28 (PDF pp.26–29)

import Definitions.Def_CosDensity_Stream

namespace CosDensity.Supplement

set_option autoImplicit false

/-!
# Real-exponent density moments

Q. Zhang, *Frequency Moments Beyond Equality: Streaming Cosine Density Moments*,
arXiv:2609.06925 (held version, sha256 f4d4df22…), §7, pp.25–28 (PDF pp.26–29).

**Formalization Note.** Section 7 permits every fixed real exponent `p > 2`. The nonnegative-cosine
and nonzero-vector hypotheses in Theorem 7.3 make every density positive, so `Real.rpow` agrees with
the ordinary positive real power used by the paper.
-/

/-- The real-exponent moment `M_p(P) = Σ_i D_i^p`. -/
noncomputable def realMoment {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (p : ℝ) (P : List E) : ℝ :=
  ∑ i : Fin P.length, (CosDensity.density P i) ^ p

end CosDensity.Supplement


