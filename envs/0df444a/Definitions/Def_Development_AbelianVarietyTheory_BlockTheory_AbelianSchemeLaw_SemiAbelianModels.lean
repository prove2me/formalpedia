-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_AbelianSchemeLaw_SemiAbelianModels
-- name    : Development_AbelianVarietyTheory_BlockTheory_AbelianSchemeLaw_SemiAbelianModels
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T15:54:05.924824+00:00
-- url     : https://prove2.me/theorems/7ca298f8-10e3-482c-9ee7-5fe77db8b161
-- title:
--   Semi Abelian Models
-- statement:
--   Definitions and structural lemmas for Semi Abelian Models, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/AbelianSchemeLaw/SemiAbelianModels.lean

import Mathlib
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
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi
namespace GlobalTheory.IndefiniteRowSideFullHecke.SemiAbelianModels
def IsExtensionByTorus {k : Type} [Field k] {T G B : Over (Spec (CommRingCat.of k))}
    [GrpObj T] [GrpObj G] [GrpObj B] (i : T ⟶ G) (q : G ⟶ B) : Prop :=
  IsTorus T ∧ IsAbelianScheme B ∧ IsMonHom i ∧ IsMonHom q ∧
    Flat q.left ∧ Surjective q.left ∧ QuasiCompact q.left ∧
    IsPullback i (toUnit T) q (η : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ B)
noncomputable abbrev fibreAlong {V F : Type} [CommRing V] [CommRing F] (f : V →+* F)
    (G : Over (Spec (CommRingCat.of V))) : Over (Spec (CommRingCat.of F)) :=
  (Over.pullback (Spec.map (CommRingCat.ofHom f))).obj G
def TorusAffineSplitsFinite : Prop :=
  ∀ (k : Type) [Field k] (T : Over (Spec (CommRingCat.of k))) [GrpObj T], IsTorus T →
    IsAffine T.left ∧
      ∃ (L : Type) (_ : Field L) (_ : Algebra k L) (_ : Module.Finite k L)
        (X : Type) (_ : AddCommGroup X) (_ : Module.Free ℤ X) (_ : Module.Finite ℤ X)
        (e : fieldBaseChange k L T ≅ splitTorus (Spec (CommRingCat.of L)) X), IsMonHom e.hom
def ResidueExtensionLifts : Prop :=
  ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    [IsAdicComplete (IsLocalRing.maximalIdeal V) V]
    (k' : Type) [Field k'] [Algebra (IsLocalRing.ResidueField V) k']
    [Module.Finite (IsLocalRing.ResidueField V) k'],
    ∃ (V' : Type) (_ : CommRing V') (_ : IsDomain V') (_ : IsDiscreteValuationRing V')
      (_ : IsAdicComplete (IsLocalRing.maximalIdeal V') V') (_ : Algebra V V'),
      Module.Finite V V' ∧ Function.Injective (algebraMap V V') ∧ IsLocalHom (algebraMap V V') ∧
        ∃ e : IsLocalRing.ResidueField V' ≃+* k', ∀ x : V,
          e (IsLocalRing.residue V' (algebraMap V V' x)) =
            algebraMap (IsLocalRing.ResidueField V) k' (IsLocalRing.residue V x)
def ExtensionQuotientAffine : Prop :=
  ∀ (k : Type) [Field k] (T G B : Over (Spec (CommRingCat.of k)))
    [GrpObj T] [GrpObj G] [GrpObj B] (i : T ⟶ G) (q : G ⟶ B),
    IsExtensionByTorus i q → IsAffineHom q.left
def ModelSemiAbelian : Prop :=
  ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    (K : Type) [Field K] [Algebra V K] [IsFractionRing V K]
    (G : Over (Spec (CommRingCat.of V))) [GrpObj G],
    IsCommMonObj G → Smooth G.hom → IsSeparated G.hom → QuasiCompact G.hom →
    IsAbelianScheme (fibreAlong (algebraMap V K) G) →
    (∃ (T B : Over (Spec (CommRingCat.of (IsLocalRing.ResidueField V))))
      (_ : GrpObj T) (_ : GrpObj B)
      (i : T ⟶ fibreAlong (IsLocalRing.residue V) G) (q : fibreAlong (IsLocalRing.residue V) G ⟶ B),
      IsExtensionByTorus i q) →
    IsSemiAbelian G
def SeamNodes : Prop :=
  TorusAffineSplitsFinite ∧ ResidueExtensionLifts ∧ ExtensionQuotientAffine ∧ ModelSemiAbelian
end GlobalTheory.IndefiniteRowSideFullHecke.SemiAbelianModels


