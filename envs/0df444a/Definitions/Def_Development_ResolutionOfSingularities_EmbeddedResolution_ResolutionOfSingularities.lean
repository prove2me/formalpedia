-- Prove2me | Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionOfSingularities
-- name    : Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionOfSingularities
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T22:49:42.336269+00:00
-- url     : https://prove2.me/theorems/88bf6672-dd79-4ddb-a67a-84b6e3a19256
-- title:
--   Resolution Of Singularities
-- statement:
--   Definitions and structural lemmas for Resolution Of Singularities, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/ResolutionOfSingularities.lean

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
section
universe u v
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
noncomputable section
namespace FunctorialResolution.EmbeddedResolution
structure SequenceOfBlowups (X : Scheme.{u}) : Type (u + 1) where
  length : ℕ
  tower : ℕᵒᵖ ⥤ Scheme.{u}
  isoZero : tower.obj (op 0) ≅ X
  center : ∀ i : ℕ, (tower.obj (op i)).IdealSheafData
  isBlowup : ∀ i : ℕ, i < length →
    Blowup.IsBlowupAlongIdealSheaf (tower.map (homOfLE (Nat.le_succ i)).op) (center i)
namespace SequenceOfBlowups
variable {X : Scheme.{u}}
abbrev schemeAt (s : SequenceOfBlowups X) (i : ℕ) : Scheme.{u} := s.tower.obj (op i)
def transitionMap (s : SequenceOfBlowups X) {i i' : ℕ} (h : i ≤ i') : s.schemeAt i' ⟶ s.schemeAt i :=
  s.tower.map (homOfLE h).op
def transitionMapSucc (s : SequenceOfBlowups X) (i : ℕ) : s.schemeAt (i + 1) ⟶ s.schemeAt i :=
  s.transitionMap (Nat.le_succ i)
def projectionToBase (s : SequenceOfBlowups X) (i : ℕ) : s.schemeAt i ⟶ X :=
  s.transitionMap (Nat.zero_le i) ≫ s.isoZero.hom
abbrev lastObj (s : SequenceOfBlowups X) : Scheme.{u} := s.schemeAt s.length
def lastStructMap (s : SequenceOfBlowups X) : s.lastObj ⟶ X := s.projectionToBase s.length
theorem transitionMap_comp_projectionToBase (s : SequenceOfBlowups X) {i i' : ℕ} (h : i ≤ i') :
    s.transitionMap h ≫ s.projectionToBase i = s.projectionToBase i' :=
  Eq.trans (Category.assoc (s.transitionMap h) (s.transitionMap (Nat.zero_le i)) s.isoZero.hom).symm
    (congrArg (fun g => g ≫ s.isoZero.hom)
      (show s.transitionMap h ≫ s.transitionMap (Nat.zero_le i) = s.transitionMap (Nat.zero_le i') from
        (s.tower.map_comp (homOfLE h).op (homOfLE (Nat.zero_le i)).op).symm))
def pullbackTransitionMap (s : SequenceOfBlowups X) {X' : Scheme.{u}} (φ : X' ⟶ X) {i i' : ℕ} (h : i ≤ i') :
    pullback φ (s.projectionToBase i') ⟶ pullback φ (s.projectionToBase i) :=
  pullback.map φ (s.projectionToBase i') φ (s.projectionToBase i) (𝟙 X') (s.transitionMap h) (𝟙 X)
    ((Category.comp_id φ).trans (Category.id_comp φ).symm)
    ((Category.comp_id (s.projectionToBase i')).trans (s.transitionMap_comp_projectionToBase h).symm)
def CentersLieOver (s : SequenceOfBlowups X) (S : Set X) : Prop :=
  ∀ i : ℕ, i < s.length → ∀ x ∈ (s.center i).support, (s.projectionToBase i).base x ∈ S
end SequenceOfBlowups
def smoothLocusComplement {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyOfFinitePresentation f] :
    TopologicalSpace.Closeds X :=
  ⟨(f.smoothLocus : Set X)ᶜ, isClosed_compl_iff.mpr f.smoothLocus.isOpen⟩
def reducedInverseImage {X X' : Scheme.{u}} (f : X' ⟶ X) (S : TopologicalSpace.Closeds X) :
    X'.IdealSheafData :=
  Scheme.IdealSheafData.vanishingIdeal
    ⟨f.base ⁻¹' (S : Set X), IsClosed.preimage f.base.hom.continuous S.2⟩
def IsRegularParameterSystem (R : Type v) [CommRing R] [IsLocalRing R] (n : ℕ)
    (x : Fin n → R) : Prop :=
  Ideal.span (Set.range x) = IsLocalRing.maximalIdeal R ∧ (n : WithBot ℕ∞) = ringKrullDim R
def IsStrictNormalCrossingsDivisor {Y : Scheme.{u}} (D : Y.IdealSheafData) : Prop :=
  ∀ y : Y, IsRegularLocalRing (Y.presheaf.stalk y) ∧
    ∃ (U : Y.affineOpens) (hy : y ∈ U.1) (n : ℕ) (f : Fin n → Γ(Y, U.1)) (J : Finset (Fin n)),
      IsRegularParameterSystem (Y.presheaf.stalk y) n
          (fun i => Y.presheaf.germ U.1 y hy (f i)) ∧
        D.ideal U = Ideal.span {∏ i ∈ J, f i}
def IsPullbackBlowupSequence {X X' : Scheme.{u}} (φ : X' ⟶ X) (s' : SequenceOfBlowups X') (s : SequenceOfBlowups X) :
    Prop :=
  ∃ (r : ℕ → ℕ)
    (e : ∀ i, i ≤ s'.length →
      @CategoryTheory.Iso Scheme.{u} _ (s'.schemeAt i) (pullback φ (s.projectionToBase (r i)))),
    (∀ i, i < s'.length → r i < s.length) ∧
    (∀ i j, j ≤ s'.length → i < j → r i < r j) ∧
    r s'.length = s.length ∧
    (∀ i, i < s.length →
      ((∃ x, x ∈ ((s.center i).comap (pullback.snd φ (s.projectionToBase i))).support) ↔
        ∃ j, j < s'.length ∧ r j = i)) ∧
    (∀ i, ∀ hi : i ≤ s'.length,
      (e i hi).hom ≫ pullback.fst φ (s.projectionToBase (r i)) = s'.projectionToBase i) ∧
    (∀ i, ∀ hi : i < s'.length, ∀ hr : r i ≤ r (i + 1),
      s'.transitionMapSucc i ≫ (e i hi.le).hom = (e (i + 1) hi).hom ≫ s.pullbackTransitionMap φ hr) ∧
    (∀ i, ∀ hi : i < s'.length,
      s'.center i
        = (s.center (r i)).comap ((e i hi.le).hom ≫ pullback.snd φ (s.projectionToBase (r i))))
abbrev specMapAlgebraMap (k K : Type u) [Field k] [Field K] [Algebra k K] :
    Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of k) :=
  Spec.map (CommRingCat.ofHom (algebraMap k K))
abbrev baseChange {X : Scheme.{u}} {k : Type u} [Field k] (p : X ⟶ Spec (CommRingCat.of k))
    (K : Type u) [Field K] [Algebra k K] : Scheme.{u} :=
  pullback p (specMapAlgebraMap k K)
abbrev baseChangeProjection {X : Scheme.{u}} {k : Type u} [Field k] (p : X ⟶ Spec (CommRingCat.of k))
    (K : Type u) [Field K] [Algebra k K] : baseChange p K ⟶ X :=
  pullback.fst p (specMapAlgebraMap k K)
abbrev baseChangeToSpec {X : Scheme.{u}} {k : Type u} [Field k]
    (p : X ⟶ Spec (CommRingCat.of k)) (K : Type u) [Field K] [Algebra k K] :
    baseChange p K ⟶ Spec (CommRingCat.of K) :=
  pullback.snd p (specMapAlgebraMap k K)
abbrev ResolutionRule : Type (u + 1) :=
  ∀ (k : Type u) [Field k] [CharZero k] (X : Scheme.{u})
    (f : X ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.LocallyOfFiniteType f]
    [AlgebraicGeometry.QuasiCompact f] [AlgebraicGeometry.IsReduced X],
    SequenceOfBlowups X
def IsStrongResolutionRule (R : ResolutionRule.{u}) : Prop :=
  ∀ (k : Type u) [Field k] [CharZero k] (X : Scheme.{u})
    (f : X ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.LocallyOfFiniteType f]
    [AlgebraicGeometry.QuasiCompact f] [AlgebraicGeometry.IsReduced X],
    AlgebraicGeometry.Smooth ((R k X f).lastStructMap ≫ f) ∧
    AlgebraicGeometry.IsProper (R k X f).lastStructMap ∧
    CategoryTheory.IsIso
      (AlgebraicGeometry.morphismRestrict (R k X f).lastStructMap f.smoothLocus) ∧
    Dense ((R k X f).lastStructMap.base ⁻¹' (f.smoothLocus : Set X)) ∧
    (R k X f).CentersLieOver ((smoothLocusComplement f : TopologicalSpace.Closeds X) : Set X) ∧
    IsStrictNormalCrossingsDivisor (reducedInverseImage (R k X f).lastStructMap (smoothLocusComplement f))
def IsCompatibleWithSmoothMorphisms (R : ResolutionRule.{u}) : Prop :=
  ∀ (k : Type u) [Field k] [CharZero k] (X X' : Scheme.{u})
    (f : X ⟶ Spec (CommRingCat.of k)) (f' : X' ⟶ Spec (CommRingCat.of k))
    [AlgebraicGeometry.LocallyOfFiniteType f] [AlgebraicGeometry.QuasiCompact f]
    [AlgebraicGeometry.IsReduced X]
    [AlgebraicGeometry.LocallyOfFiniteType f'] [AlgebraicGeometry.QuasiCompact f']
    [AlgebraicGeometry.IsReduced X']
    (φ : X' ⟶ X) (r : ℕ) [AlgebraicGeometry.SmoothOfRelativeDimension r φ],
    φ ≫ f = f' → IsPullbackBlowupSequence φ (R k X' f') (R k X f)
def IsCompatibleWithFieldExtension (R : ResolutionRule.{u}) : Prop :=
  ∀ (k : Type u) [Field k] [CharZero k] (X : Scheme.{u})
    (f : X ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.LocallyOfFiniteType f]
    [AlgebraicGeometry.QuasiCompact f] [AlgebraicGeometry.IsReduced X]
    (K : Type u) [Field K] [CharZero K] [Algebra k K]
    [AlgebraicGeometry.IsReduced (baseChange f K)],
    IsPullbackBlowupSequence (baseChangeProjection f K)
      (R K (baseChange f K) (baseChangeToSpec f K)) (R k X f)
def StrongResolutionOfSingularitiesCharZero : Prop :=
  ∃ R : ResolutionRule.{u},
    IsStrongResolutionRule R ∧ IsCompatibleWithSmoothMorphisms R ∧ IsCompatibleWithFieldExtension R
end FunctorialResolution.EmbeddedResolution
end
end


