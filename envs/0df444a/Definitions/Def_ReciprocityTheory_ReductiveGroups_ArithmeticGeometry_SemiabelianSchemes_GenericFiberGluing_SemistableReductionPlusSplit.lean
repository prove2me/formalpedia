-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_GenericFiberGluing_SemistableReductionPlusSplit
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_GenericFiberGluing_SemistableReductionPlusSplit
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T12:58:16.338249+00:00
-- url     : https://prove2.me/theorems/3b3eea99-b297-40a7-be71-b9d12871ed33
-- title:
--   Semistable Reduction Plus Split
-- statement:
--   Definitions and structural lemmas for Semistable Reduction Plus Split, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SemiabelianSchemes/GenericFiberGluing/SemistableReductionPlusSplit.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_AbelianSchemeQuotients_IsAbelianScheme
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_SplitTori_IsTorus
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
noncomputable section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
namespace ReciprocityTheory.ChartRestriction.G.Semi
abbrev specMap (A B : Type) [CommRing A] [CommRing B] [Algebra A B] :
    Spec (CommRingCat.of B) ⟶ Spec (CommRingCat.of A) :=
  Spec.map (CommRingCat.ofHom (algebraMap A B))
abbrev baseChange (A B : Type) [CommRing A] [CommRing B] [Algebra A B]
    (X : Over (Spec (CommRingCat.of A))) : Over (Spec (CommRingCat.of B)) :=
  (Over.pullback (specMap A B)).obj X
abbrev genFibre (W : Type) [CommRing W] [IsDomain W] (X : Over (Spec (CommRingCat.of W))) :
    Over (Spec (CommRingCat.of (FractionRing W))) :=
  baseChange W (FractionRing W) X
abbrev specialFibre (W : Type) [CommRing W] [IsLocalRing W] (X : Over (Spec (CommRingCat.of W))) :
    Over (Spec (CommRingCat.of (IsLocalRing.ResidueField W))) :=
  baseChange W (IsLocalRing.ResidueField W) X
abbrev restrictToGeneric (W : Type) [CommRing W] [IsDomain W] {X : Over (Spec (CommRingCat.of W))}
    (x : 𝟙_ (Over (Spec (CommRingCat.of W))) ⟶ X) :
    𝟙_ (Over (Spec (CommRingCat.of (FractionRing W)))) ⟶ genFibre W X :=
  (Functor.Monoidal.εIso (Over.pullback (specMap W (FractionRing W)))).hom ≫
    (Over.pullback (specMap W (FractionRing W))).map x
structure TorusExt {K : Type u} [Field K] (G : Over (Spec (.of K))) [GrpObj G] where

  B : Over (Spec (.of K))
  [grpB : GrpObj B]
  isAbelian : IsAbelianScheme B

  q : G ⟶ B
  q_hom : IsMonHom q
  q_flat : Flat q.left
  q_surjective : Surjective q.left
  q_quasiCompact : QuasiCompact q.left

  T₀ : Over (Spec (.of K))
  [grpT : GrpObj T₀]
  isTorus : IsTorus T₀
  i : T₀ ⟶ G
  i_hom : IsMonHom i

  isKernel : IsPullback i (toUnit _) q (η : 𝟙_ _ ⟶ B)
attribute [instance] TorusExt.grpB TorusExt.grpT
def HasExtProp (W : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W]
    (G : Over (Spec (CommRingCat.of W))) [GrpObj G] : Prop :=
  ∀ (H : Over (Spec (CommRingCat.of W))) [GrpObj H] [IsCommMonObj H],
    Smooth H.hom → LocallyOfFiniteType H.hom → QuasiCompact H.hom →
    ConnectedSpace (specialFibre W H).left →
    ∀ φ : genFibre W H ⟶ genFibre W G, IsMonHom φ →
      ∃! ψ : H ⟶ G,
        IsMonHom ψ ∧ (Over.pullback (specMap W (FractionRing W))).map ψ = φ
def HasMultProp (W : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W]
    (G : Over (Spec (CommRingCat.of W))) [GrpObj G] : Prop :=
  ∀ a : 𝟙_ (Over (Spec (CommRingCat.of (FractionRing W)))) ⟶ genFibre W G,
    ∃ n : ℕ, 0 < n ∧ ∃ x : 𝟙_ (Over (Spec (CommRingCat.of W))) ⟶ G,
      restrictToGeneric W x = a ≫ mulN (genFibre W G) n
def ExtAndMultiples (V' : Type) [CommRing V'] (G : Over (Spec (CommRingCat.of V'))) [GrpObj G]
    (W : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Algebra V' W] : Prop :=
  HasExtProp W (baseChange V' W G) ∧ HasMultProp W (baseChange V' W G)
def SemistableReductionPlusSplit : Prop :=
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
      Nonempty (TorusExtension (specialFibre V' G)) ∧
      ∀ (W : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W]
        [IsAdicComplete (IsLocalRing.maximalIdeal W) W] [Algebra V' W],
        Function.Injective (algebraMap V' W) → IsLocalHom (algebraMap V' W) →
        ExtAndMultiples V' G W
def SemistableReductionPlus : Prop :=
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
      Nonempty (TorusExt (specialFibre V' G)) ∧
      ∀ (W : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W]
        [IsAdicComplete (IsLocalRing.maximalIdeal W) W] [Algebra V' W],
        Function.Injective (algebraMap V' W) → IsLocalHom (algebraMap V' W) →
        ExtAndMultiples V' G W
end ReciprocityTheory.ChartRestriction.G.Semi


