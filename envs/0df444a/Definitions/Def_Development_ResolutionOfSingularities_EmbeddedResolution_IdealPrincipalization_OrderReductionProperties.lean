-- Prove2me | Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IdealPrincipalization_OrderReductionProperties
-- name    : Development_ResolutionOfSingularities_EmbeddedResolution_IdealPrincipalization_OrderReductionProperties
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-24T13:53:31.805893+00:00
-- url     : https://prove2.me/theorems/166c3b41-0b5c-4e31-bc9e-3fa3d2931ee1
-- title:
--   Order Reduction Properties
-- statement:
--   Definitions and structural lemmas for Order Reduction Properties, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/IdealPrincipalization/OrderReductionProperties.lean

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IteratedBlowups_BlowupSequenceRelations
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_StrictTransform
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_StrictNormalCrossings
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_IdealSheafOrder
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_MaximalContactHypersurfaces_MaxContactIdeal
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IdealPrincipalization_PrincipalizationCertificateMonotone
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IdealPrincipalization_PrincipalizationCertificate
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IdealPrincipalization_FunctorialPrincipalization
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IdealPrincipalization_MarkedBlowupSequence_IdealBlowupSequence
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IdealPrincipalization_MarkedBlowupSequence_MarkedSequenceOfBlowups
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionOfSingularities
import Theorems.Thm_Derivation_liftToLocalization_algebraMap
import Theorems.Thm_Derivation_mapToLocalization_algebraMap
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_MarkedSequenceOfBlowups_toMarkedSequence_lastIdeal
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_MarkedSequenceOfBlowups_toMarkedSequence_toSequenceOfBlowups
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_derivIdealSheafIterate_ideal
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_derivIdealSheafIterate_zero
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_derivIdealSheaf_ideal
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_maxContactIdeal_eq_derivIdealSheafIterate
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Derivation.liftToLocalization_algebraMap
attribute [local simp] Derivation.mapToLocalization_algebraMap
attribute [local simp] FunctorialResolution.EmbeddedResolution.MarkedSequenceOfBlowups.toMarkedSequence_lastIdeal
attribute [local simp] FunctorialResolution.EmbeddedResolution.MarkedSequenceOfBlowups.toMarkedSequence_toSequenceOfBlowups
attribute [local simp] FunctorialResolution.EmbeddedResolution.derivIdealSheafIterate_ideal
attribute [local simp] FunctorialResolution.EmbeddedResolution.derivIdealSheafIterate_zero
attribute [local simp] FunctorialResolution.EmbeddedResolution.derivIdealSheaf_ideal
attribute [local simp] FunctorialResolution.EmbeddedResolution.maxContactIdeal_eq_derivIdealSheafIterate


set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
noncomputable section
namespace FunctorialResolution.EmbeddedResolution
def kerSubschemeIso {X Y : Scheme.{u}} (f : X ⟶ Y)
    [AlgebraicGeometry.IsClosedImmersion f] : (Scheme.Hom.ker f).subscheme ≅ X :=
  (asIso (Scheme.Hom.toImage f)).symm
namespace MarkedIdealWithBoundary
def pullbackAlong (T : MarkedIdealWithBoundary.{u}) (Y : Scheme.{u})
    (q : Y ⟶ Spec (CommRingCat.of T.base)) (h : Y ⟶ T.scheme) : MarkedIdealWithBoundary.{u} where
  base := T.base
  instField := T.instField
  scheme := Y
  structMap := q
  ideal := T.ideal.comap h
  mult := T.mult
  boundary := T.boundary.map (fun D => D.comap h)
@[simp] theorem pullbackAlong_baseField (T : MarkedIdealWithBoundary.{u}) (Y : Scheme.{u})
    (q : Y ⟶ Spec (CommRingCat.of T.base)) (h : Y ⟶ T.scheme) :
    (T.pullbackAlong Y q h).base = T.base := rfl
@[simp] theorem pullbackAlong_scheme (T : MarkedIdealWithBoundary.{u}) (Y : Scheme.{u})
    (q : Y ⟶ Spec (CommRingCat.of T.base)) (h : Y ⟶ T.scheme) :
    (T.pullbackAlong Y q h).scheme = Y := rfl
@[simp] theorem pullbackAlong_mult (T : MarkedIdealWithBoundary.{u}) (Y : Scheme.{u})
    (q : Y ⟶ Spec (CommRingCat.of T.base)) (h : Y ⟶ T.scheme) :
    (T.pullbackAlong Y q h).mult = T.mult := rfl
def baseChange (T : MarkedIdealWithBoundary.{u}) (L : Type u) [Field L] (f : T.base →+* L) :
    MarkedIdealWithBoundary.{u} where
  base := L
  scheme := pullback T.structMap (specMapOfFieldHom T.base L f)
  structMap := pullback.snd T.structMap (specMapOfFieldHom T.base L f)
  ideal := T.ideal.comap (pullback.fst T.structMap (specMapOfFieldHom T.base L f))
  mult := T.mult
  boundary :=
    T.boundary.map (fun D => D.comap (pullback.fst T.structMap (specMapOfFieldHom T.base L f)))
@[simp] theorem baseChange_baseField (T : MarkedIdealWithBoundary.{u}) (L : Type u) [Field L]
    (f : T.base →+* L) : (T.baseChange L f).base = L := rfl
@[simp] theorem baseChange_mult (T : MarkedIdealWithBoundary.{u}) (L : Type u) [Field L]
    (f : T.base →+* L) : (T.baseChange L f).mult = T.mult := rfl
def withSchemeIdealBoundary (T : MarkedIdealWithBoundary.{u}) (Y : Scheme.{u}) (q : Y ⟶ Spec (CommRingCat.of T.base))
    (J : Y.IdealSheafData) (E : List Y.IdealSheafData) : MarkedIdealWithBoundary.{u} where
  base := T.base
  instField := T.instField
  scheme := Y
  structMap := q
  ideal := J
  mult := T.mult
  boundary := E
@[simp] theorem withSchemeIdealBoundary_baseField (T : MarkedIdealWithBoundary.{u}) (Y : Scheme.{u})
    (q : Y ⟶ Spec (CommRingCat.of T.base)) (J : Y.IdealSheafData)
    (E : List Y.IdealSheafData) : (T.withSchemeIdealBoundary Y q J E).base = T.base := rfl
@[simp] theorem withSchemeIdealBoundary_scheme (T : MarkedIdealWithBoundary.{u}) (Y : Scheme.{u})
    (q : Y ⟶ Spec (CommRingCat.of T.base)) (J : Y.IdealSheafData)
    (E : List Y.IdealSheafData) : (T.withSchemeIdealBoundary Y q J E).scheme = Y := rfl
@[simp] theorem withSchemeIdealBoundary_mult (T : MarkedIdealWithBoundary.{u}) (Y : Scheme.{u})
    (q : Y ⟶ Spec (CommRingCat.of T.base)) (J : Y.IdealSheafData)
    (E : List Y.IdealSheafData) : (T.withSchemeIdealBoundary Y q J E).mult = T.mult := rfl
def withBoundary (T : MarkedIdealWithBoundary.{u}) (E : List T.scheme.IdealSheafData) :
    MarkedIdealWithBoundary.{u} where
  base := T.base
  instField := T.instField
  scheme := T.scheme
  structMap := T.structMap
  ideal := T.ideal
  mult := T.mult
  boundary := E
@[simp] theorem withBoundary_baseField (T : MarkedIdealWithBoundary.{u}) (E : List T.scheme.IdealSheafData) :
    (T.withBoundary E).base = T.base := rfl
@[simp] theorem withBoundary_scheme (T : MarkedIdealWithBoundary.{u}) (E : List T.scheme.IdealSheafData) :
    (T.withBoundary E).scheme = T.scheme := rfl
@[simp] theorem withBoundary_structureMorphism (T : MarkedIdealWithBoundary.{u})
    (E : List T.scheme.IdealSheafData) : (T.withBoundary E).structMap = T.structMap := rfl
@[simp] theorem withBoundary_ideal (T : MarkedIdealWithBoundary.{u}) (E : List T.scheme.IdealSheafData) :
    (T.withBoundary E).ideal = T.ideal := rfl
@[simp] theorem withBoundary_mult (T : MarkedIdealWithBoundary.{u}) (E : List T.scheme.IdealSheafData) :
    (T.withBoundary E).mult = T.mult := rfl
@[simp] theorem withBoundary_boundary (T : MarkedIdealWithBoundary.{u})
    (E : List T.scheme.IdealSheafData) : (T.withBoundary E).boundary = E := rfl
@[simp] theorem withBoundary_dim (T : MarkedIdealWithBoundary.{u}) (E : List T.scheme.IdealSheafData) :
    (T.withBoundary E).krullDimSucc = T.krullDimSucc := rfl
@[simp] theorem withBoundary_self (T : MarkedIdealWithBoundary.{u}) :
    T.withBoundary T.boundary = T := rfl
def nontrivialPart {X : Scheme.{u}} (E : List X.IdealSheafData) : List X.IdealSheafData :=
  E.filter (fun D => !(@decide (D = ⊤) (Classical.propDecidable _)))
def SameNontrivialBoundary {X : Scheme.{u}} (E E' : List X.IdealSheafData) : Prop :=
  nontrivialPart E = nontrivialPart E'
theorem nontrivialPart_map_nontrivialPart {X Y : Scheme.{u}}
    (f : X.IdealSheafData → Y.IdealSheafData) (hf : f ⊤ = ⊤) (L : List X.IdealSheafData) :
    nontrivialPart ((nontrivialPart L).map f) = nontrivialPart (L.map f) := by
  have hcons_top : ∀ {Z : Scheme.{u}} {a : Z.IdealSheafData}, a = ⊤ →
      ∀ M : List Z.IdealSheafData, nontrivialPart (a :: M) = nontrivialPart M := by
    intro Z a ha M
    have hb : (@decide (a = ⊤) (Classical.propDecidable (a = ⊤))) = true := by simp [ha]
    simp [nontrivialPart, hb]
  have hcons_ne : ∀ {Z : Scheme.{u}} {a : Z.IdealSheafData}, ¬ a = ⊤ →
      ∀ M : List Z.IdealSheafData, nontrivialPart (a :: M) = a :: nontrivialPart M := by
    intro Z a ha M
    have hb : (@decide (a = ⊤) (Classical.propDecidable (a = ⊤))) = false := by simp [ha]
    simp [nontrivialPart, hb]
  induction L with
  | nil => simp [nontrivialPart]
  | cons a L ih =>
    by_cases ha : a = ⊤
    · have hfa : f a = ⊤ := by rw [ha]; exact hf
      rw [hcons_top ha L, List.map_cons, hcons_top hfa (L.map f), ih]
    · by_cases hfa : f a = ⊤
      · rw [hcons_ne ha L, List.map_cons, List.map_cons,
          hcons_top hfa ((nontrivialPart L).map f), hcons_top hfa (L.map f), ih]
      · rw [hcons_ne ha L, List.map_cons, List.map_cons,
          hcons_ne hfa ((nontrivialPart L).map f), hcons_ne hfa (L.map f), ih]
theorem SameNontrivialBoundary.map {X Y : Scheme.{u}} (f : X.IdealSheafData → Y.IdealSheafData)
    (hf : f ⊤ = ⊤) {L L' : List X.IdealSheafData} (h : SameNontrivialBoundary L L') :
    SameNontrivialBoundary (L.map f) (L'.map f) := by
  have e : nontrivialPart L = nontrivialPart L' := h
  show nontrivialPart (L.map f) = nontrivialPart (L'.map f)
  rw [← nontrivialPart_map_nontrivialPart f hf L, ← nontrivialPart_map_nontrivialPart f hf L', e]
def AdmissibleUnderBoundaryReplacement : Prop :=
  ∀ (T : MarkedIdealWithBoundary.{u}) (E' : List T.scheme.IdealSheafData), T.IsAdmissible →
    SameNontrivialBoundary T.boundary E' → (T.withBoundary E').IsAdmissible
def IsOrderBoundedByMult (T : MarkedIdealWithBoundary.{u}) : Prop :=
  ∀ x : ↥T.scheme, orderAt T.ideal x ≤ (T.mult : ℕ∞)
def IsBalanced (T : MarkedIdealWithBoundary.{u})
    (hft : AlgebraicGeometry.LocallyOfFiniteType T.structMap) : Prop :=
  haveI : AlgebraicGeometry.LocallyOfFiniteType T.structMap := hft
  haveI : IsNoetherianRing T.base := inferInstance
  IsDerivBalanced T.base T.structMap T.ideal T.mult
end MarkedIdealWithBoundary
namespace MarkedSequenceOfBlowups
variable {k : Type u} [Field k] {X : Scheme.{u}} {p : X ⟶ Spec (CommRingCat.of k)}
  {I : X.IdealSheafData} {m : ℕ} {E : List X.IdealSheafData}
def boundaryLocus (s : MarkedSequenceOfBlowups p I m E) (t : ℕ) : Set ↥(s.toSequenceOfBlowups.schemeAt t) :=
  ⋃ D ∈ s.boundary t, ((D.support : Set ↥(s.toSequenceOfBlowups.schemeAt t)))
def otherBoundaryLocus (s : MarkedSequenceOfBlowups p I m E) (j t : ℕ) :
    Set ↥(s.toSequenceOfBlowups.schemeAt t) :=
  ⋃ (i : Fin (s.boundary t).length) (_ : (i : ℕ) ≠ j),
    (((s.boundary t).get i).support : Set ↥(s.toSequenceOfBlowups.schemeAt t))
end MarkedSequenceOfBlowups
structure IsMaxOrderReduction (P : ℕ → Prop) (A B : PrincipalizationAssignment.{u}) : Prop where
  cert : ∀ T : MarkedIdealWithBoundary.{u}, T.IsAdmissible → P T.krullDimSucc →
    ∀ i, i < (A T).toSequenceOfBlowups.length →
      PrincipalizationCertificate ((A T).toSequenceOfBlowups.schemeAt i) ((A T).projectionToSpec i) ((A T).ideal i) T.mult
        ((A T).boundaryLocus i) ((A T).toSequenceOfBlowups.center i)
  orderRed_equiv : ∀ T : MarkedIdealWithBoundary.{u}, T.IsAdmissible → P T.krullDimSucc →
    T.boundary = [] → T.IsOrderBoundedByMult →
    (A T).toSequenceOfBlowups.Isomorphic (B T).toSequenceOfBlowups
  base_change : ∀ T : MarkedIdealWithBoundary.{u}, T.IsAdmissible → P T.krullDimSucc →
    ∀ (L : Type u) [Field L] [CharZero L] (f : T.base →+* L)
      (E' : List (T.baseChange L f).scheme.IdealSheafData),
      MarkedIdealWithBoundary.SameNontrivialBoundary (T.baseChange L f).boundary E' →
      ((T.baseChange L f).withBoundary E').IsAdmissible →
      P ((T.baseChange L f).withBoundary E').krullDimSucc →
      IsPullbackBlowupSequence (pullback.fst T.structMap (specMapOfFieldHom T.base L f))
        (A ((T.baseChange L f).withBoundary E')).toSequenceOfBlowups (A T).toSequenceOfBlowups
  base_change_strict : ∀ T : MarkedIdealWithBoundary.{u}, T.IsAdmissible → P T.krullDimSucc →
    ∀ (L : Type u) [Field L] [CharZero L] (f : T.base →+* L)
      (E' : List (T.baseChange L f).scheme.IdealSheafData),
      MarkedIdealWithBoundary.SameNontrivialBoundary (T.baseChange L f).boundary E' →
      ((T.baseChange L f).withBoundary E').IsAdmissible →
      P ((T.baseChange L f).withBoundary E').krullDimSucc →
      IsStrictPullbackBlowupSeq (pullback.fst T.structMap (specMapOfFieldHom T.base L f))
        (A ((T.baseChange L f).withBoundary E')).toSequenceOfBlowups (A T).toSequenceOfBlowups
  center_nonempty : ∀ T : MarkedIdealWithBoundary.{u}, T.IsAdmissible → P T.krullDimSucc →
    ∀ i, i < (A T).toSequenceOfBlowups.length →
      (((A T).toSequenceOfBlowups.center i).support : Set ↥((A T).toSequenceOfBlowups.schemeAt i)).Nonempty
  resolves : ∀ T : MarkedIdealWithBoundary.{u}, T.IsAdmissible → P T.krullDimSucc → (A T).IsResolution
  smooth_pullback : ∀ T : MarkedIdealWithBoundary.{u}, T.IsAdmissible → P T.krullDimSucc →
    ∀ (Y : Scheme.{u}) (q : Y ⟶ Spec (CommRingCat.of T.base)) (h : Y ⟶ T.scheme)
      [AlgebraicGeometry.Smooth h], h ≫ T.structMap = q →
    ∀ E' : List Y.IdealSheafData,
      MarkedIdealWithBoundary.SameNontrivialBoundary (T.pullbackAlong Y q h).boundary E' →
      ((T.pullbackAlong Y q h).withBoundary E').IsAdmissible →
      P ((T.pullbackAlong Y q h).withBoundary E').krullDimSucc →
      IsPullbackBlowupSequence h (A ((T.pullbackAlong Y q h).withBoundary E')).toSequenceOfBlowups
        (A T).toSequenceOfBlowups
  smooth_pullback_strict : ∀ T : MarkedIdealWithBoundary.{u}, T.IsAdmissible → P T.krullDimSucc →
    ∀ (Y : Scheme.{u}) (q : Y ⟶ Spec (CommRingCat.of T.base)) (h : Y ⟶ T.scheme)
      [AlgebraicGeometry.Smooth h] [AlgebraicGeometry.Surjective h], h ≫ T.structMap = q →
    ∀ E' : List Y.IdealSheafData,
      MarkedIdealWithBoundary.SameNontrivialBoundary (T.pullbackAlong Y q h).boundary E' →
      ((T.pullbackAlong Y q h).withBoundary E').IsAdmissible →
      P ((T.pullbackAlong Y q h).withBoundary E').krullDimSucc →
      IsStrictPullbackBlowupSeq h (A ((T.pullbackAlong Y q h).withBoundary E')).toSequenceOfBlowups
        (A T).toSequenceOfBlowups
  trivial_of_coSupport_empty : ∀ T : MarkedIdealWithBoundary.{u}, T.IsAdmissible → P T.krullDimSucc →
    orderAtLeastLocus T.ideal T.mult = ∅ → (A T).toSequenceOfBlowups.length = 0
structure IsOrderReduction (P : ℕ → Prop) (A B : PrincipalizationAssignment.{u}) : Prop where
  cert : ∀ T : MarkedIdealWithBoundary.{u}, T.IsAdmissible → P T.krullDimSucc → T.IsOrderBoundedByMult →
    ∀ i, i < (A T).toSequenceOfBlowups.length →
      OrderCertificate ((A T).toSequenceOfBlowups.schemeAt i) ((A T).projectionToSpec i) ((A T).ideal i) T.mult
        ((A T).boundaryLocus i) ((A T).toSequenceOfBlowups.center i)
  base_change : ∀ T : MarkedIdealWithBoundary.{u}, T.IsAdmissible → P T.krullDimSucc → T.IsOrderBoundedByMult →
    ∀ (L : Type u) [Field L] [CharZero L] (f : T.base →+* L)
      (E' : List (T.baseChange L f).scheme.IdealSheafData),
      MarkedIdealWithBoundary.SameNontrivialBoundary (T.baseChange L f).boundary E' →
      ((T.baseChange L f).withBoundary E').IsAdmissible →
      P ((T.baseChange L f).withBoundary E').krullDimSucc →
      ((T.baseChange L f).withBoundary E').IsOrderBoundedByMult →
      IsPullbackBlowupSequence (pullback.fst T.structMap (specMapOfFieldHom T.base L f))
        (A ((T.baseChange L f).withBoundary E')).toSequenceOfBlowups (A T).toSequenceOfBlowups
  base_change_strict : ∀ T : MarkedIdealWithBoundary.{u}, T.IsAdmissible → P T.krullDimSucc → T.IsOrderBoundedByMult →
    ∀ (L : Type u) [Field L] [CharZero L] (f : T.base →+* L)
      (E' : List (T.baseChange L f).scheme.IdealSheafData),
      MarkedIdealWithBoundary.SameNontrivialBoundary (T.baseChange L f).boundary E' →
      ((T.baseChange L f).withBoundary E').IsAdmissible →
      P ((T.baseChange L f).withBoundary E').krullDimSucc →
      ((T.baseChange L f).withBoundary E').IsOrderBoundedByMult →
      IsStrictPullbackBlowupSeq (pullback.fst T.structMap (specMapOfFieldHom T.base L f))
        (A ((T.baseChange L f).withBoundary E')).toSequenceOfBlowups (A T).toSequenceOfBlowups
  pushforward : ∀ T : MarkedIdealWithBoundary.{u}, T.IsAdmissible → P T.krullDimSucc → T.IsOrderBoundedByMult →
    T.boundary = [] → T.mult = 1 →
    ∀ (Y : Scheme.{u}) (q : Y ⟶ Spec (CommRingCat.of T.base)) (e : Y ⟶ T.scheme)
      [AlgebraicGeometry.IsClosedImmersion e], e ≫ T.structMap = q →
      IsSmoothDivisor T.structMap (Scheme.Hom.ker e) →
    ∀ J : Y.IdealSheafData,
      (T.withSchemeIdealBoundary Y q J ([] : List Y.IdealSheafData)).IsAdmissible →
      (T.withSchemeIdealBoundary Y q J ([] : List Y.IdealSheafData)).krullDimSucc < T.krullDimSucc →
      T.ideal = imageIdealSheaf e J →
      IsPushforwardBlowupSeq e (B (T.withSchemeIdealBoundary Y q J ([] : List Y.IdealSheafData))).toSequenceOfBlowups
        (A T).toSequenceOfBlowups
  order_le : ∀ T : MarkedIdealWithBoundary.{u}, T.IsAdmissible → P T.krullDimSucc → T.IsOrderBoundedByMult →
    ∀ i, i ≤ (A T).toSequenceOfBlowups.length →
      ∀ x : ↥((A T).toSequenceOfBlowups.schemeAt i), orderAt ((A T).ideal i) x ≤ (T.mult : ℕ∞)
  center_nonempty : ∀ T : MarkedIdealWithBoundary.{u}, T.IsAdmissible → P T.krullDimSucc → T.IsOrderBoundedByMult →
    ∀ i, i < (A T).toSequenceOfBlowups.length →
      (((A T).toSequenceOfBlowups.center i).support : Set ↥((A T).toSequenceOfBlowups.schemeAt i)).Nonempty
  resolves : ∀ T : MarkedIdealWithBoundary.{u}, T.IsAdmissible → P T.krullDimSucc → T.IsOrderBoundedByMult → (A T).IsResolution
  smooth_pullback : ∀ T : MarkedIdealWithBoundary.{u}, T.IsAdmissible → P T.krullDimSucc → T.IsOrderBoundedByMult →
    ∀ (Y : Scheme.{u}) (q : Y ⟶ Spec (CommRingCat.of T.base)) (h : Y ⟶ T.scheme)
      [AlgebraicGeometry.Smooth h], h ≫ T.structMap = q →
    ∀ E' : List Y.IdealSheafData,
      MarkedIdealWithBoundary.SameNontrivialBoundary (T.pullbackAlong Y q h).boundary E' →
      ((T.pullbackAlong Y q h).withBoundary E').IsAdmissible →
      P ((T.pullbackAlong Y q h).withBoundary E').krullDimSucc →
      ((T.pullbackAlong Y q h).withBoundary E').IsOrderBoundedByMult →
      IsPullbackBlowupSequence h (A ((T.pullbackAlong Y q h).withBoundary E')).toSequenceOfBlowups
        (A T).toSequenceOfBlowups
  smooth_pullback_strict : ∀ T : MarkedIdealWithBoundary.{u}, T.IsAdmissible → P T.krullDimSucc → T.IsOrderBoundedByMult →
    ∀ (Y : Scheme.{u}) (q : Y ⟶ Spec (CommRingCat.of T.base)) (h : Y ⟶ T.scheme)
      [AlgebraicGeometry.Smooth h] [AlgebraicGeometry.Surjective h], h ≫ T.structMap = q →
    ∀ E' : List Y.IdealSheafData,
      MarkedIdealWithBoundary.SameNontrivialBoundary (T.pullbackAlong Y q h).boundary E' →
      ((T.pullbackAlong Y q h).withBoundary E').IsAdmissible →
      P ((T.pullbackAlong Y q h).withBoundary E').krullDimSucc →
      ((T.pullbackAlong Y q h).withBoundary E').IsOrderBoundedByMult →
      IsStrictPullbackBlowupSeq h (A ((T.pullbackAlong Y q h).withBoundary E')).toSequenceOfBlowups
        (A T).toSequenceOfBlowups
  trivial_of_coSupport_empty : ∀ T : MarkedIdealWithBoundary.{u}, T.IsAdmissible → P T.krullDimSucc → T.IsOrderBoundedByMult →
    orderAtLeastLocus T.ideal T.mult = ∅ → (A T).toSequenceOfBlowups.length = 0
structure IsBoundaryDivisorReduction (P : ℕ → Prop) (j : ℕ) (A B : PrincipalizationAssignment.{u}) : Prop where
  base_change : ∀ (T : MarkedIdealWithBoundary.{u}) (hV : T.IsAdmissible), P T.krullDimSucc → T.IsOrderBoundedByMult →
    T.IsBalanced hV.locallyOfFiniteType → j < T.boundary.length →
    ∀ (L : Type u) [Field L] [CharZero L] (f : T.base →+* L)
      (E' : List (T.baseChange L f).scheme.IdealSheafData),
      MarkedIdealWithBoundary.SameNontrivialBoundary (T.baseChange L f).boundary E' →
      E'.take (j + 1) = (T.baseChange L f).boundary.take (j + 1) →
    ∀ hV' : ((T.baseChange L f).withBoundary E').IsAdmissible,
      P ((T.baseChange L f).withBoundary E').krullDimSucc →
      ((T.baseChange L f).withBoundary E').IsOrderBoundedByMult →
      ((T.baseChange L f).withBoundary E').IsBalanced hV'.locallyOfFiniteType →
      j < ((T.baseChange L f).withBoundary E').boundary.length →
      IsPullbackBlowupSequence (pullback.fst T.structMap (specMapOfFieldHom T.base L f))
        (A ((T.baseChange L f).withBoundary E')).toSequenceOfBlowups (A T).toSequenceOfBlowups
  base_change_strict : ∀ (T : MarkedIdealWithBoundary.{u}) (hV : T.IsAdmissible), P T.krullDimSucc → T.IsOrderBoundedByMult →
    T.IsBalanced hV.locallyOfFiniteType → j < T.boundary.length →
    ∀ (L : Type u) [Field L] [CharZero L] (f : T.base →+* L)
      (E' : List (T.baseChange L f).scheme.IdealSheafData),
      MarkedIdealWithBoundary.SameNontrivialBoundary (T.baseChange L f).boundary E' →
      E'.take (j + 1) = (T.baseChange L f).boundary.take (j + 1) →
    ∀ hV' : ((T.baseChange L f).withBoundary E').IsAdmissible,
      P ((T.baseChange L f).withBoundary E').krullDimSucc →
      ((T.baseChange L f).withBoundary E').IsOrderBoundedByMult →
      ((T.baseChange L f).withBoundary E').IsBalanced hV'.locallyOfFiniteType →
      j < ((T.baseChange L f).withBoundary E').boundary.length →
      IsStrictPullbackBlowupSeq (pullback.fst T.structMap (specMapOfFieldHom T.base L f))
        (A ((T.baseChange L f).withBoundary E')).toSequenceOfBlowups (A T).toSequenceOfBlowups
  order_le : ∀ (T : MarkedIdealWithBoundary.{u}) (hV : T.IsAdmissible), P T.krullDimSucc → T.IsOrderBoundedByMult →
    T.IsBalanced hV.locallyOfFiniteType → j < T.boundary.length →
    ∀ i, i ≤ (A T).toSequenceOfBlowups.length →
      ∀ x : ↥((A T).toSequenceOfBlowups.schemeAt i), orderAt ((A T).ideal i) x ≤ (T.mult : ℕ∞)
  center_nonempty : ∀ (T : MarkedIdealWithBoundary.{u}) (hV : T.IsAdmissible), P T.krullDimSucc → T.IsOrderBoundedByMult →
    T.IsBalanced hV.locallyOfFiniteType → j < T.boundary.length →
    ∀ i, i < (A T).toSequenceOfBlowups.length →
      (((A T).toSequenceOfBlowups.center i).support : Set ↥((A T).toSequenceOfBlowups.schemeAt i)).Nonempty
  pushforward : ∀ (T : MarkedIdealWithBoundary.{u}) (hV : T.IsAdmissible), P T.krullDimSucc → T.IsOrderBoundedByMult →
    T.IsBalanced hV.locallyOfFiniteType → ∀ hj : j < T.boundary.length, T.mult = 1 →
    ∀ J : (T.boundary.get ⟨j, hj⟩).subscheme.IdealSheafData,
      (T.withSchemeIdealBoundary (T.boundary.get ⟨j, hj⟩).subscheme
          ((T.boundary.get ⟨j, hj⟩).subschemeι ≫ T.structMap) J
          ((T.boundary.eraseIdx j).map
            (fun D => D.comap (T.boundary.get ⟨j, hj⟩).subschemeι))).IsAdmissible →
      (T.withSchemeIdealBoundary (T.boundary.get ⟨j, hj⟩).subscheme
          ((T.boundary.get ⟨j, hj⟩).subschemeι ≫ T.structMap) J
          ((T.boundary.eraseIdx j).map
            (fun D => D.comap (T.boundary.get ⟨j, hj⟩).subschemeι))).krullDimSucc < T.krullDimSucc →
      T.ideal = imageIdealSheaf (T.boundary.get ⟨j, hj⟩).subschemeι J →
      IsPushforwardBlowupSeq (T.boundary.get ⟨j, hj⟩).subschemeι
        (B (T.withSchemeIdealBoundary (T.boundary.get ⟨j, hj⟩).subscheme
            ((T.boundary.get ⟨j, hj⟩).subschemeι ≫ T.structMap) J
            ((T.boundary.eraseIdx j).map
              (fun D => D.comap (T.boundary.get ⟨j, hj⟩).subschemeι)))).toSequenceOfBlowups
        (A T).toSequenceOfBlowups
  shape : ∀ (T : MarkedIdealWithBoundary.{u}) (hV : T.IsAdmissible), P T.krullDimSucc → T.IsOrderBoundedByMult →
    T.IsBalanced hV.locallyOfFiniteType → ∀ hj : j < T.boundary.length,
    ∃ (D : ∀ t : ℕ, ((A T).toSequenceOfBlowups.schemeAt t).IdealSheafData) (b : Bool),
      (∀ t ≤ (A T).toSequenceOfBlowups.length, IsSmoothDivisor ((A T).projectionToSpec t) (D t)) ∧
      D 0 = (T.boundary.get ⟨j, hj⟩).comap (A T).toSequenceOfBlowups.isoZero.hom ∧
      (∀ t < (A T).toSequenceOfBlowups.length,
        (((A T).toSequenceOfBlowups.center t).support : Set ↥((A T).toSequenceOfBlowups.schemeAt t)) ⊆
          (((D t).support : Set ↥((A T).toSequenceOfBlowups.schemeAt t)))) ∧
      (b = true →
        0 < (A T).toSequenceOfBlowups.length ∧
        IsOpen ((D 0).subschemeι.base ⁻¹'
          ((((A T).toSequenceOfBlowups.center 0).support : Set ↥((A T).toSequenceOfBlowups.schemeAt 0)))) ∧
        D 1 = (D 0).comap ((A T).toSequenceOfBlowups.transitionMapSucc 0)) ∧
      (∀ t < (A T).toSequenceOfBlowups.length, ¬ (b = true ∧ t = 0) →
        D (t + 1) = Blowup.strictTransform ((A T).toSequenceOfBlowups.transitionMapSucc t)
          ((A T).toSequenceOfBlowups.center t) (D t)) ∧
      (orderAtLeastLocus (A T).lastIdeal T.mult ∩
        (((D (A T).toSequenceOfBlowups.length).support :
          Set ↥((A T).toSequenceOfBlowups.schemeAt (A T).toSequenceOfBlowups.length)))) = ∅ ∧
      (∀ t < (A T).toSequenceOfBlowups.length, ¬ (b = true ∧ t = 0) →
        ∃ J : (D t).subscheme.IdealSheafData,
          NonzeroOnComponents J ∧
          (∀ x : ↥(D t).subscheme,
            (D t).subschemeι.base x ∉ (A T).otherBoundaryLocus j t →
            ∃ V : (D t).subscheme.Opens, x ∈ V ∧
              J.comap V.ι = (((A T).ideal t).comap (D t).subschemeι).comap V.ι) ∧
          PrincipalizationCertificate (D t).subscheme ((D t).subschemeι ≫ (A T).projectionToSpec t) J T.mult
            ((D t).subschemeι.base ⁻¹' (A T).otherBoundaryLocus j t)
            (((A T).toSequenceOfBlowups.center t).comap (D t).subschemeι))
  smooth_pullback : ∀ (T : MarkedIdealWithBoundary.{u}) (hV : T.IsAdmissible), P T.krullDimSucc → T.IsOrderBoundedByMult →
    T.IsBalanced hV.locallyOfFiniteType → j < T.boundary.length →
    ∀ (Y : Scheme.{u}) (q : Y ⟶ Spec (CommRingCat.of T.base)) (h : Y ⟶ T.scheme)
      [AlgebraicGeometry.Smooth h], h ≫ T.structMap = q →
    ∀ E' : List Y.IdealSheafData,
      MarkedIdealWithBoundary.SameNontrivialBoundary (T.pullbackAlong Y q h).boundary E' →
      E'.take (j + 1) = (T.pullbackAlong Y q h).boundary.take (j + 1) →
    ∀ hV' : ((T.pullbackAlong Y q h).withBoundary E').IsAdmissible,
      P ((T.pullbackAlong Y q h).withBoundary E').krullDimSucc →
      ((T.pullbackAlong Y q h).withBoundary E').IsOrderBoundedByMult →
      ((T.pullbackAlong Y q h).withBoundary E').IsBalanced hV'.locallyOfFiniteType →
      j < ((T.pullbackAlong Y q h).withBoundary E').boundary.length →
      IsPullbackBlowupSequence h (A ((T.pullbackAlong Y q h).withBoundary E')).toSequenceOfBlowups
        (A T).toSequenceOfBlowups
  smooth_pullback_strict : ∀ (T : MarkedIdealWithBoundary.{u}) (hV : T.IsAdmissible), P T.krullDimSucc → T.IsOrderBoundedByMult →
    T.IsBalanced hV.locallyOfFiniteType → j < T.boundary.length →
    ∀ (Y : Scheme.{u}) (q : Y ⟶ Spec (CommRingCat.of T.base)) (h : Y ⟶ T.scheme)
      [AlgebraicGeometry.Smooth h] [AlgebraicGeometry.Surjective h], h ≫ T.structMap = q →
    ∀ E' : List Y.IdealSheafData,
      MarkedIdealWithBoundary.SameNontrivialBoundary (T.pullbackAlong Y q h).boundary E' →
      E'.take (j + 1) = (T.pullbackAlong Y q h).boundary.take (j + 1) →
    ∀ hV' : ((T.pullbackAlong Y q h).withBoundary E').IsAdmissible,
      P ((T.pullbackAlong Y q h).withBoundary E').krullDimSucc →
      ((T.pullbackAlong Y q h).withBoundary E').IsOrderBoundedByMult →
      ((T.pullbackAlong Y q h).withBoundary E').IsBalanced hV'.locallyOfFiniteType →
      j < ((T.pullbackAlong Y q h).withBoundary E').boundary.length →
      IsStrictPullbackBlowupSeq h (A ((T.pullbackAlong Y q h).withBoundary E')).toSequenceOfBlowups
        (A T).toSequenceOfBlowups
  trivial_of_coSupport_empty : ∀ (T : MarkedIdealWithBoundary.{u}) (hV : T.IsAdmissible), P T.krullDimSucc →
    T.IsOrderBoundedByMult → T.IsBalanced hV.locallyOfFiniteType → j < T.boundary.length →
    orderAtLeastLocus T.ideal T.mult = ∅ → (A T).toSequenceOfBlowups.length = 0
structure IsBoundaryPositionInvariant (P : ℕ → Prop) (A : ℕ → PrincipalizationAssignment.{u}) : Prop where
  shift : ∀ (T : MarkedIdealWithBoundary.{u}), P T.krullDimSucc → T.IsOrderBoundedByMult →
    ∀ hft : AlgebraicGeometry.LocallyOfFiniteType T.structMap, T.IsBalanced hft →
    ∀ (E₁ E₂ E₁' E₂' : List T.scheme.IdealSheafData) (D : T.scheme.IdealSheafData),
      MarkedIdealWithBoundary.SameNontrivialBoundary E₁ E₁' → MarkedIdealWithBoundary.SameNontrivialBoundary E₂ E₂' →
      (T.withBoundary (E₁ ++ D :: E₂)).IsAdmissible →
      (T.withBoundary (E₁' ++ D :: E₂')).IsAdmissible →
      ((A E₁.length) (T.withBoundary (E₁ ++ D :: E₂))).toSequenceOfBlowups.Isomorphic
        ((A E₁'.length) (T.withBoundary (E₁' ++ D :: E₂'))).toSequenceOfBlowups
end FunctorialResolution.EmbeddedResolution


