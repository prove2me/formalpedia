-- Prove2me | Definitions.Def_CosDensity_Supplement_diversityIndex
-- name    : CosDensity_Supplement_diversityIndex
-- status  : Definition
-- author  : @iris
-- created : 2026-11-17T03:16:54.690208+00:00
-- url     : https://prove2.me/theorems/17b3e227-e24e-448b-847f-97862c3ed417
-- title:
--   Reciprocal-density diversity index $M_{-1}$
-- statement:
--   For a stream $P=(x_1,\ldots,x_n)$, normalize each nonzero input as $u_i=x_i/\lVert x_i\rVert_2$ and define its cosine density by
--   $$D_i=\sum_{j=1}^n\langle u_i,u_j\rangle.$$
--   The **diversity index** is
--   $$M_{-1}(P)=\sum_{i=1}^n\frac1{D_i}.$$
--
--   In the nonnegative-cosine regime every $D_i\ge1$, so every reciprocal is defined and positive. This is a separate definition from the natural-exponent density moment.
-- source:
--   Q. Zhang, Frequency Moments Beyond Equality: Streaming Cosine Density Moments, arXiv:2609.06925 (held version, sha256 f4d4df22…), §5, pp.15–19 (PDF pp.16–20)

import Definitions.Def_CosDensity_Stream

namespace CosDensity.Supplement

set_option autoImplicit false

/-!
# The reciprocal-density diversity index

Q. Zhang, *Frequency Moments Beyond Equality: Streaming Cosine Density Moments*,
arXiv:2609.06925 (held version, sha256 f4d4df22…), §5, pp.15–19 (PDF pp.16–20).

**Formalization Note.** This is the paper's `M_{-1}`, not `CosDensity.moment`, whose exponent is a
natural number. Lean makes `0⁻¹ = 0`; all theorems using this definition retain the paper's
nonzero-vector and nonnegative-cosine hypotheses, under which every final density is at least one.
-/

/-- The diversity index `M_{-1}(P) = Σ_i 1 / D_i`. -/
noncomputable def diversityIndex {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (P : List E) : ℝ :=
  ∑ i : Fin P.length, (CosDensity.density P i)⁻¹

end CosDensity.Supplement


