-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_DenseClosedPoints
-- name    : Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_DenseClosedPoints
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T12:16:28.09679+00:00
-- url     : https://prove2.me/theorems/a07cdb14-94cf-40ac-a318-fff9b23eb70f
-- title:
--   Dense Closed Points
-- statement:
--   Definitions and structural lemmas for Dense Closed Points, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CubicalLineBundles/DenseClosedPoints.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp valAt valAt')
namespace GlobalTheory.SchemeHomsFromPoints
noncomputable def ev {X : Scheme.{0}} (x : Sp ℂ ⟶ X) (W : X.Opens) (e : ⊤ ≤ x ⁻¹ᵁ W) :
    Γ(X, W) ⟶ CommRingCat.of ℂ :=
  x.appLE W ⊤ e ≫ (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom
end GlobalTheory.SchemeHomsFromPoints


