-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_GenericFiberGluing_PlusConditionToZeroCondition
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_GenericFiberGluing_PlusConditionToZeroCondition
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T13:01:43.148087+00:00
-- url     : https://prove2.me/theorems/411d0a15-fb8f-490f-97e6-f9e2482a15b6
-- title:
--   Plus Condition To Zero Condition
-- statement:
--   Definitions and structural lemmas for Plus Condition To Zero Condition, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SemiabelianSchemes/GenericFiberGluing/PlusConditionToZeroCondition.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_GenericFiberGluing_SemistableReductionPlusSplit
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
namespace ReciprocityTheory.ChartRestriction.G.Semi
def SemistableReductionZero : Prop :=
  ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    [IsAdicComplete (IsLocalRing.maximalIdeal V) V]
    (K : Type) [Field K] [CharZero K] [Algebra V K] [IsFractionRing V K]
    (A : Over (Spec (CommRingCat.of K))) [GrpObj A], IsAbelianScheme A →
  ∃ (K' : Type) (_ : Field K') (_ : Algebra K K') (_ : FiniteDimensional K K')
    (V' : Type) (_ : CommRing V') (_ : IsDomain V') (_ : IsDiscreteValuationRing V')
    (_ : Algebra V V') (_ : Algebra V' K') (_ : IsFractionRing V' K'),
    Module.Finite V V' ∧ Function.Injective (algebraMap V V') ∧
    (algebraMap V' K').comp (algebraMap V V') = (algebraMap K K').comp (algebraMap V K) ∧
    ∃ (G : Over (Spec (CommRingCat.of V'))) (_ : GrpObj G),
      IsCommMonObj G ∧ Smooth G.hom ∧ IsSeparated G.hom ∧ QuasiCompact G.hom ∧
      (∃ e : baseChange V' K' G ≅ baseChange K K' A, IsMonHom e.hom) ∧
      Nonempty (TorusExt (specialFibre V' G))
end ReciprocityTheory.ChartRestriction.G.Semi


