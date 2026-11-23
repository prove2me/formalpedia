-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_GenericFiberGluing_SemistableCompleteSplit
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_GenericFiberGluing_SemistableCompleteSplit
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T13:03:24.492546+00:00
-- url     : https://prove2.me/theorems/fdc3c903-437c-464f-bcdb-92cce2211abd
-- title:
--   Semistable Complete Split
-- statement:
--   Definitions and structural lemmas for Semistable Complete Split, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SemiabelianSchemes/GenericFiberGluing/SemistableCompleteSplit.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_GenericFiberGluing_SemistableReductionPlusSplit
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_GenericFiberGluing_PlusConditionToZeroCondition
import Mathlib.AlgebraicGeometry.Morphisms.Affine
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
namespace ReciprocityTheory.ChartRestriction.G.Semi
def NaSt : Prop :=
  ∀ (k : Type u) [Field k] (T : Over (Spec (.of k))) [GrpObj T], IsTorus T →
    IsAffineHom T.hom ∧
    ∃ (k' : Type u) (_ : Field k') (_ : Algebra k k') (_ : FiniteDimensional k k')
      (X : Type u) (_ : AddCommGroup X) (_ : Module.Free ℤ X) (_ : Module.Finite ℤ X)
      (e : fieldBaseChange k k' T ≅ splitTorus (Spec (.of k')) X), IsMonHom e.hom
def NbSt : Prop :=
  ∀ (V' : Type) [CommRing V'] [IsDomain V'] [IsDiscreteValuationRing V']
    [IsAdicComplete (IsLocalRing.maximalIdeal V') V']
    (k'' : Type) [Field k''] [Algebra (IsLocalRing.ResidueField V') k'']
    [FiniteDimensional (IsLocalRing.ResidueField V') k''],
  ∃ (V'' : Type) (_ : CommRing V'') (_ : IsDomain V'') (_ : IsDiscreteValuationRing V'')
    (_ : IsAdicComplete (IsLocalRing.maximalIdeal V'') V'') (_ : Algebra V' V''),
    Module.Finite V' V'' ∧ Function.Injective (algebraMap V' V'') ∧
    ∃ (_ : IsLocalHom (algebraMap V' V'')) (e : k'' ≃+* IsLocalRing.ResidueField V''),
      e.toRingHom.comp (algebraMap (IsLocalRing.ResidueField V') k'') =
        IsLocalRing.ResidueField.map (algebraMap V' V'')
def NcSt : Prop := SemistableReductionPlus → SemistableReductionPlusSplit
def NdSt : Prop :=
  ∀ (K : Type u) [Field K] (G : Over (Spec (.of K))) [GrpObj G] (E : TorusExt G),
    IsAffineHom E.q.left
def NfSt : Prop :=
  ∀ (V' : Type) [CommRing V'] [IsDomain V'] [IsDiscreteValuationRing V']
    (K' : Type) [Field K'] [Algebra V' K'] [IsFractionRing V' K']
    (A : Over (Spec (CommRingCat.of K'))) [GrpObj A], IsAbelianScheme A →
    ∀ (G : Over (Spec (CommRingCat.of V'))) [GrpObj G],
      IsCommMonObj G → Smooth G.hom → IsSeparated G.hom → QuasiCompact G.hom →
      (∃ e : baseChange V' K' G ≅ A, IsMonHom e.hom) →
      Nonempty (TorusExt (specialFibre V' G)) → IsSemiAbelian G
def SemistableCompleteSplit : Prop :=
  ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    [IsAdicComplete (IsLocalRing.maximalIdeal V) V]
    (K : Type) [Field K] [CharZero K] [Algebra V K] [IsFractionRing V K]
    (A : Over (Spec (CommRingCat.of K))) [GrpObj A], IsAbelianScheme A →
  ∃ (K' : Type) (_ : Field K') (_ : Algebra K K') (_ : FiniteDimensional K K')
    (V' : Type) (_ : CommRing V') (_ : IsDomain V') (_ : IsDiscreteValuationRing V')
    (_ : IsAdicComplete (IsLocalRing.maximalIdeal V') V')
    (_ : Algebra V V') (_ : Algebra V' K') (_ : IsFractionRing V' K'),
    Algebra.IsIntegral V V' ∧
    (algebraMap V' K').comp (algebraMap V V') = (algebraMap K K').comp (algebraMap V K) ∧
    ∃ (G : Over (Spec (CommRingCat.of V'))) (_ : GrpObj G),
      IsSemiAbelian G ∧
      (∃ e : baseChange V' K' G ≅ baseChange K K' A, IsMonHom e.hom) ∧
      Nonempty (TorusExtension (specialFibre V' G))
def NcZeroSt : Prop := SemistableReductionZero → SemistableCompleteSplit
end ReciprocityTheory.ChartRestriction.G.Semi


