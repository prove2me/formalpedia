-- Prove2me | Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_NormalizedCompositumEdges
-- name    : QEC_Coding_AlgebraicGeometry_Towers_NormalizedCompositumEdges
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T19:09:06.879849+00:00
-- url     : https://prove2.me/theorems/b33ddf0f-1130-4f83-9c5e-cacd5218c3fe
-- title:
--   Normalized Compositum Edges
-- statement:
--   Definitions and structural lemmas for Normalized Compositum Edges, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/NormalizedCompositumEdges.lean

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_IntermediateIntegralModels
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_QuadraticCompositumCell
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differents_RelativeTower
set_option autoImplicit false
open IntermediateField
open scoped QEC.Coding.AlgebraicGeometry.IntermediateIntegralModels
namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
attribute [local instance 2500] Algebra.toSMul Algebra.toModule
variable (A F E : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [_root_.Field F] [_root_.Field E] [Algebra A F] [IsFractionRing A F]
    [Algebra F E] [Algebra A E] [IsScalarTower A F E]
    [FiniteDimensional F E] [Algebra.IsSeparable F E]
    [Algebra F256 F] [Algebra F256 E] [IsScalarTower F256 F E]
    [Module.Finite A (integralClosure A E)]
    (Q : IsDedekindDomain.HeightOneSpectrum (integralClosure A E))
local notation "C" => IntermediateIntegralModels.Model A F E
local notation "P" => IntermediateIntegralModels.prime A F E Q
def NormalizedEdge (K L : IntermediateField F E) : Prop :=
  ∃ (a : K) (y : E),
    y ^ 2 + y = (a : E) ∧
    ((heightOnePlace (k := F256) (K := K) (P K)).order a = -1 ∨
      0 ≤ (heightOnePlace (k := F256) (K := K) (P K)).order a) ∧
    (K⟮y⟯).restrictScalars F = L
theorem NormalizedEdge.le {K L : IntermediateField F E}
    (h : NormalizedEdge A F E Q K L) : K ≤ L := by
  obtain ⟨a, y, _, _, hL⟩ := h
  rw [← hL, IntermediateField.restrictScalars_adjoin_eq_sup]
  exact le_sup_left
abbrev NormalizedRefinement (K L : IntermediateField F E) : Prop :=
  Relation.ReflTransGen (NormalizedEdge A F E Q) K L
theorem NormalizedRefinement.le {K L : IntermediateField F E}
    (h : NormalizedRefinement A F E Q K L) : K ≤ L := by
  induction h with
  | refl => exact le_rfl
  | tail h hstep ih => exact ih.trans (hstep.le A F E Q)
end
end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth


