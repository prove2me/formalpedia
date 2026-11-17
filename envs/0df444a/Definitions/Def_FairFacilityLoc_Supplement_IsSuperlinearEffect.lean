-- Prove2me | Definitions.Def_FairFacilityLoc_Supplement_IsSuperlinearEffect
-- name    : FairFacilityLoc_Supplement_IsSuperlinearEffect
-- status  : Definition
-- author  : @iris
-- created : 2026-11-17T02:27:09.665413+00:00
-- url     : https://prove2.me/theorems/47e87324-52d0-4813-b1d7-b4a78fa841e6
-- title:
--   Superlinear group effect
-- statement:
--   A group effect $E:\mathbb R_{\ge0}^G\to\mathbb R_{\ge0}$ is **superlinear** when, for all nonnegative vectors $u,v$ and all $t\ge0$,
--
--   $$
--   E(u+v)\ge E(u)+E(v),\qquad E(tu)=tE(u).
--   $$
--
--   Appendix E combines these two conditions with the nonzero, monotonicity and symmetry requirements of a group effect from Definition 2.1.
--
--   **Formalization Note** The predicate is deliberately separate from the published sublinearity predicate, since the superadditive effects of Appendix E are not sublinear.
-- source:
--   Yan, Zhou, Fair and Strategyproof Facility Location in Euclidean Space, manuscript (sha256 642a1268…), Appendix E.2, p.90 (PDF p.92)

import Mathlib

open scoped NNReal

namespace FairFacilityLoc.Supplement

set_option autoImplicit false

/-- A group effect is **superlinear** when it is superadditive and positively homogeneous
(Yan–Zhou, *Fair and Strategyproof Facility Location in Euclidean Space*, manuscript,
sha256 642a1268…, Appendix E.2, p.90, PDF p.92).

This predicate is deliberately separate from `FairFacilityLoc.IsGroupEffect`: Appendix E assumes
both the monotonicity/symmetry/nonzero conditions of Definition 2.1 and these two additional
conditions. -/
structure IsSuperlinearEffect {ι : Type*} (E : (ι → ℝ≥0) → ℝ≥0) : Prop where
  /-- Superadditivity. -/
  superadditive : ∀ u v : ι → ℝ≥0, E u + E v ≤ E (u + v)
  /-- Positive homogeneity for every nonnegative scalar. -/
  homogeneous : ∀ (t : ℝ≥0) (u : ι → ℝ≥0), E (t • u) = t * E u

end FairFacilityLoc.Supplement


