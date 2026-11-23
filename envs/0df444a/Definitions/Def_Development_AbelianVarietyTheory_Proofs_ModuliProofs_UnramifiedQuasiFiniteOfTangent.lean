-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_UnramifiedQuasiFiniteOfTangent
-- name    : Development_AbelianVarietyTheory_Proofs_ModuliProofs_UnramifiedQuasiFiniteOfTangent
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T16:20:26.823994+00:00
-- url     : https://prove2.me/theorems/79b51cfb-d6a5-4fee-bc97-6864974e12c1
-- title:
--   Unramified Quasi Finite Of Tangent
-- statement:
--   Definitions and structural lemmas for Unramified Quasi Finite Of Tangent, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/UnramifiedQuasiFiniteOfTangent.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsSeparatedOfIsQProjOver
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
namespace GlobalTheory.TangentCriterion
noncomputable def dualOfDerivation {A B K : Type} [CommRing A] [CommRing B] [Field K] [Algebra A B]
    [Algebra B K] [Algebra A K] (D : Derivation A B K) : B →+* DualNumber K where
  toFun b := TrivSqZeroExt.inl (algebraMap B K b) + TrivSqZeroExt.inr (D b)
  map_one' := by ext <;> simp
  map_mul' a b := by
    ext
    · simp
    · simp only [TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr, zero_add,
        DualNumber.snd_mul, TrivSqZeroExt.fst_add, TrivSqZeroExt.fst_inl, TrivSqZeroExt.fst_inr,
        add_zero, Derivation.leibniz, Algebra.smul_def]
      ring
  map_zero' := by ext <;> simp
  map_add' a b := by ext <;> simp
end GlobalTheory.TangentCriterion


