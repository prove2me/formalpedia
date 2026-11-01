-- Prove2me | Definitions.Def_MaxEntCont_faceDim
-- name    : MaxEntCont_faceDim
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T17:17:49.525031+00:00
-- url     : https://prove2.me/theorems/dfe7a5d4-48c5-4285-a3af-447a09eccf73
-- title:
--   Dimension $\dim F(x)$ of the face function
-- statement:
--   Let $C$ be a convex subset of a real vector space and $x\in C$. Write $F(x)$ for the face of $C$ that contains $x$ in its relative interior (the face function of $C$). The number
--   $$
--   \dim F(x)
--   $$
--   is the dimension of the affine hull of $F(x)$, i.e. the dimension of the linear space spanned by the differences $y-z$, $y,z\in F(x)$. Extremal points have dimension $0$, and a point in the relative interior of $C$ has $\dim F(x)=\dim C$.
--
--   The function $x\mapsto\dim F(x)$ appears in Papadopoulou's characterization of stable convex bodies and in the dimension inequality of the main theorem.
--
--   **Formalization Note** $F(x)$ is the platform definition `OAI.CanonicalFace198.minFace C x`, the intersection of all convex extreme subsets of $C$ containing $x$, i.e. the smallest face through $x$; Fact 5.3 (`MaxEntCont.fact_5_3`) identifies it with the face containing $x$ in its relative interior. The dimension is `Module.finrank ℝ (vectorSpan ℝ (minFace C x))`. For $x\notin C$ the value is meaningless (`minFace C x` is the whole space); every statement of the mission uses it only at points of $C$.
-- source:
--   Rodman, Spitkovsky, Szkoła, Weis, Continuity of the maximum-entropy inference, arXiv:1502.02018v1, Fact 5.4(3) and Theorem 5.6(2), pp. 13–14

import Mathlib
import Definitions.Def_TriangleFace

namespace MaxEntCont

open OAI.CanonicalFace198

/-- **Dimension of the face** `dim F(x)` (Rodman, Spitkovsky, Szkoła, Weis, *Continuity of the maximum-entropy inference*, arXiv:1502.02018v1, Fact 5.4(3) and Theorem 5.6(2), pp. 13–14):
the dimension of the affine hull of the face `F(x)` of `C` containing `x` in its relative
interior, i.e. the finite rank of the direction `vectorSpan ℝ F(x)`.

**Formalization Note** The face function `F(x)` is the platform definition
`OAI.CanonicalFace198.minFace C x`, the intersection of all convex extreme subsets of `C`
containing `x` (the smallest face through `x`); Fact 5.3 (`MaxEntCont.fact_5_3`) identifies it
with the paper's `F(x)` for `x ∈ C`. For `x ∉ C` the value is junk (`minFace C x = univ`); every
statement of the mission evaluates `faceDim C x` only at points `x ∈ C`. A point has dimension 0. -/
noncomputable def faceDim {X : Type*} [AddCommGroup X] [Module ℝ X] (C : Set X) (x : X) : ℕ :=
  Module.finrank ℝ (vectorSpan ℝ (minFace C x))

end MaxEntCont


