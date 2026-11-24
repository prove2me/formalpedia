-- Prove2me | Definitions.Def_Development_ResolutionOfSingularities_Statements
-- name    : Development_ResolutionOfSingularities_Statements
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T22:52:48.863804+00:00
-- url     : https://prove2.me/theorems/1d3b529c-eff6-465c-a9a9-817005dac260
-- title:
--   Statements
-- statement:
--   Definitions and structural lemmas for Statements, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/Statements.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
namespace FunctorialResolution
def IsEffectiveCartier {X : Scheme.{u}} (I : X.IdealSheafData) : Prop :=
  ∀ x : X, ∃ (U : X.affineOpens) (f : Γ(X, U.1)),
    x ∈ U.1 ∧ f ∈ nonZeroDivisors Γ(X, U.1) ∧ I.ideal U = Ideal.span {f}
def IsBlowup {X X' : Scheme.{u}} (π : X' ⟶ X) (I : X.IdealSheafData) : Prop :=
  IsEffectiveCartier (I.comap π) ∧
    ∀ (T : Scheme.{u}) (g : T ⟶ X), IsEffectiveCartier (I.comap g) → ∃! h : T ⟶ X', h ≫ π = g
def IsRegularSystemOfParameters (R : Type u) [CommRing R] [IsLocalRing R] (n : ℕ) (x : Fin n → R) : Prop :=
  Ideal.span (Set.range x) = IsLocalRing.maximalIdeal R ∧ (n : WithBot ℕ∞) = ringKrullDim R
def IsStrictNormalCrossingsAt {Y : Scheme.{u}} (D : Y.IdealSheafData) (y : Y) : Prop :=
  IsRegularLocalRing (Y.presheaf.stalk y) ∧
    ∃ (U : Y.affineOpens) (hy : y ∈ U.1) (n : ℕ) (f : Fin n → Γ(Y, U.1)) (J : Finset (Fin n)),
      IsRegularSystemOfParameters (Y.presheaf.stalk y) n (fun i => Y.presheaf.germ U.1 y hy (f i)) ∧
        D.ideal U = Ideal.span {∏ i ∈ J, f i}
def IsStrictNormalCrossings {Y : Scheme.{u}} (D : Y.IdealSheafData) : Prop :=
  ∀ y : Y, IsStrictNormalCrossingsAt D y
section Resolution
open Opposite
noncomputable section
structure BlowupSequence (X : Scheme.{u}) : Type (u + 1) where

  length : ℕ

  tower : ℕᵒᵖ ⥤ Scheme.{u}

  isoZero : tower.obj (op 0) ≅ X

  center : ∀ i : ℕ, (tower.obj (op i)).IdealSheafData

  isBlowup : ∀ i : ℕ, i < length → IsBlowup (tower.map (homOfLE (Nat.le_succ i)).op) (center i)
namespace BlowupSequence
variable {X : Scheme.{u}}
abbrev obj (s : BlowupSequence X) (i : ℕ) : Scheme.{u} := s.tower.obj (op i)
def down (s : BlowupSequence X) {i i' : ℕ} (h : i ≤ i') : s.obj i' ⟶ s.obj i :=
  s.tower.map (homOfLE h).op
def blowupMap (s : BlowupSequence X) (i : ℕ) : s.obj (i + 1) ⟶ s.obj i :=
  s.down (Nat.le_succ i)
def structMap (s : BlowupSequence X) (i : ℕ) : s.obj i ⟶ X :=
  s.down (Nat.zero_le i) ≫ s.isoZero.hom
abbrev top (s : BlowupSequence X) : Scheme.{u} := s.obj s.length
def topMap (s : BlowupSequence X) : s.top ⟶ X := s.structMap s.length
theorem structMap_down (s : BlowupSequence X) {i i' : ℕ} (h : i ≤ i') :
    s.down h ≫ s.structMap i = s.structMap i' :=
  Eq.trans (Category.assoc (s.down h) (s.down (Nat.zero_le i)) s.isoZero.hom).symm
    (congrArg (fun g => g ≫ s.isoZero.hom)
      (show s.down h ≫ s.down (Nat.zero_le i) = s.down (Nat.zero_le i') from
        (s.tower.map_comp (homOfLE h).op (homOfLE (Nat.zero_le i)).op).symm))
def pullbackMap (s : BlowupSequence X) {X' : Scheme.{u}} (φ : X' ⟶ X) {i i' : ℕ} (h : i ≤ i') :
    pullback φ (s.structMap i') ⟶ pullback φ (s.structMap i) :=
  pullback.map φ (s.structMap i') φ (s.structMap i) (𝟙 X') (s.down h) (𝟙 X)
    ((Category.comp_id φ).trans (Category.id_comp φ).symm)
    ((Category.comp_id (s.structMap i')).trans (s.structMap_down h).symm)
def CentersOver (s : BlowupSequence X) (S : Set X) : Prop :=
  ∀ i : ℕ, i < s.length → ∀ x ∈ (s.center i).support, (s.structMap i).base x ∈ S
end BlowupSequence
def nonSmoothLocus {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyOfFinitePresentation f] :
    TopologicalSpace.Closeds X :=
  ⟨(f.smoothLocus : Set X)ᶜ, isClosed_compl_iff.mpr f.smoothLocus.isOpen⟩
def reducedPreimage {X X' : Scheme.{u}} (f : X' ⟶ X) (S : TopologicalSpace.Closeds X) : X'.IdealSheafData :=
  Scheme.IdealSheafData.vanishingIdeal ⟨f.base ⁻¹' (S : Set X), IsClosed.preimage f.base.hom.continuous S.2⟩
def IsPullbackSequence {X X' : Scheme.{u}} (φ : X' ⟶ X) (s' : BlowupSequence X') (s : BlowupSequence X) : Prop :=
  ∃ (r : ℕ → ℕ)
    (e : ∀ i, i ≤ s'.length → @Iso Scheme.{u} _ (s'.obj i) (pullback φ (s.structMap (r i)))),
    (∀ i, i < s'.length → r i < s.length) ∧
    (∀ i j, j ≤ s'.length → i < j → r i < r j) ∧
    r s'.length = s.length ∧
    (∀ i, i < s.length →
      ((∃ x, x ∈ ((s.center i).comap (pullback.snd φ (s.structMap i))).support) ↔
        ∃ j, j < s'.length ∧ r j = i)) ∧
    (∀ i, ∀ hi : i ≤ s'.length, (e i hi).hom ≫ pullback.fst φ (s.structMap (r i)) = s'.structMap i) ∧
    (∀ i, ∀ hi : i < s'.length, ∀ hr : r i ≤ r (i + 1),
      s'.blowupMap i ≫ (e i hi.le).hom = (e (i + 1) hi).hom ≫ s.pullbackMap φ hr) ∧
    (∀ i, ∀ hi : i < s'.length,
      s'.center i = (s.center (r i)).comap ((e i hi.le).hom ≫ pullback.snd φ (s.structMap (r i))))
abbrev specFieldExtension (k K : Type u) [Field k] [Field K] [Algebra k K] :
    Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of k) :=
  Spec.map (CommRingCat.ofHom (algebraMap k K))
abbrev fieldBaseChange {X : Scheme.{u}} {k : Type u} [Field k] (f : X ⟶ Spec (CommRingCat.of k))
    (K : Type u) [Field K] [Algebra k K] : Scheme.{u} :=
  pullback f (specFieldExtension k K)
abbrev fieldBaseChangeProj {X : Scheme.{u}} {k : Type u} [Field k] (f : X ⟶ Spec (CommRingCat.of k))
    (K : Type u) [Field K] [Algebra k K] : fieldBaseChange f K ⟶ X :=
  pullback.fst f (specFieldExtension k K)
abbrev fieldBaseChangeStructMap {X : Scheme.{u}} {k : Type u} [Field k] (f : X ⟶ Spec (CommRingCat.of k))
    (K : Type u) [Field K] [Algebra k K] : fieldBaseChange f K ⟶ Spec (CommRingCat.of K) :=
  pullback.snd f (specFieldExtension k K)
abbrev ResolutionRuleCharZero : Type (u + 1) :=
  ∀ (k : Type u) [Field k] [CharZero k] (X : Scheme.{u}) (f : X ⟶ Spec (CommRingCat.of k))
    [LocallyOfFiniteType f] [QuasiCompact f] [IsReduced X], BlowupSequence X
def IsResolutionRuleCharZero (R : ResolutionRuleCharZero.{u}) : Prop :=
  ∀ (k : Type u) [Field k] [CharZero k] (X : Scheme.{u}) (f : X ⟶ Spec (CommRingCat.of k))
    [LocallyOfFiniteType f] [QuasiCompact f] [IsReduced X],
    Smooth ((R k X f).topMap ≫ f) ∧ IsProper (R k X f).topMap ∧
    IsIso (morphismRestrict (R k X f).topMap f.smoothLocus) ∧
    Dense ((R k X f).topMap.base ⁻¹' (f.smoothLocus : Set X)) ∧
    (R k X f).CentersOver ((nonSmoothLocus f : TopologicalSpace.Closeds X) : Set X) ∧
    IsStrictNormalCrossings (reducedPreimage (R k X f).topMap (nonSmoothLocus f))
def IsSmoothFunctorialRule (R : ResolutionRuleCharZero.{u}) : Prop :=
  ∀ (k : Type u) [Field k] [CharZero k] (X X' : Scheme.{u})
    (f : X ⟶ Spec (CommRingCat.of k)) (f' : X' ⟶ Spec (CommRingCat.of k))
    [LocallyOfFiniteType f] [QuasiCompact f] [IsReduced X]
    [LocallyOfFiniteType f'] [QuasiCompact f'] [IsReduced X']
    (φ : X' ⟶ X) (r : ℕ) [SmoothOfRelativeDimension r φ],
    φ ≫ f = f' → IsPullbackSequence φ (R k X' f') (R k X f)
def IsFieldExtensionFunctorialRule (R : ResolutionRuleCharZero.{u}) : Prop :=
  ∀ (k : Type u) [Field k] [CharZero k] (X : Scheme.{u}) (f : X ⟶ Spec (CommRingCat.of k))
    [LocallyOfFiniteType f] [QuasiCompact f] [IsReduced X]
    (K : Type u) [Field K] [CharZero K] [Algebra k K] [IsReduced (fieldBaseChange f K)],
    IsPullbackSequence (fieldBaseChangeProj f K)
      (R K (fieldBaseChange f K) (fieldBaseChangeStructMap f K)) (R k X f)
def FunctorialResolutionCharZero : Prop :=
  ∃ R : ResolutionRuleCharZero.{u},
    IsResolutionRuleCharZero R ∧ IsSmoothFunctorialRule R ∧ IsFieldExtensionFunctorialRule R
end
end Resolution
noncomputable section
def IsNonzeroOnComponents {X : Scheme.{u}} (I : X.IdealSheafData) : Prop :=
  ∀ T ∈ irreducibleComponents X, ¬ T ⊆ (I.support : Set X)
abbrev affineSpaceOverField (k : Type u) [Field k] (m : ℕ) : Scheme.{u} :=
  AffineSpace (ULift.{u} (Fin m)) (Spec (CommRingCat.of k))
def coordinateSubspaceIdeal (k : Type u) [Field k] (m : ℕ) (S : Finset (Fin m)) :
    (affineSpaceOverField k m).IdealSheafData :=
  Scheme.IdealSheafData.ofIdealTop
    (Ideal.span ((fun i : Fin m => AffineSpace.coord (Spec (CommRingCat.of k)) (ULift.up i)) '' (S : Set (Fin m))))
def IsSmoothDivisor {X : Scheme.{u}} {k : Type u} [Field k] (p : X ⟶ Spec (CommRingCat.of k))
    (D : X.IdealSheafData) : Prop :=
  IsEffectiveCartier D ∧ Smooth (D.subschemeι ≫ p)
def HasSimpleNormalCrossingsAt {X : Scheme.{u}} {k : Type u} [Field k] (p : X ⟶ Spec (CommRingCat.of k))
    (E : List X.IdealSheafData) (x : X) : Prop :=
  ∃ (U : X.Opens) (_ : x ∈ U) (m : ℕ) (c : U.toScheme ⟶ affineSpaceOverField k m)
    (_ : c ≫ (affineSpaceOverField k m ↘ Spec (CommRingCat.of k)) = U.ι ≫ p) (_ : Etale c)
    (a : ℕ → Option (Fin m)),
    (∀ i < E.length, ∀ j < E.length, ∀ t : Fin m, a i = some t → a j = some t → i = j) ∧
    (∀ i, ∀ h : i < E.length, a i = none → (E[i]'h).comap U.ι = ⊤) ∧
    (∀ i, ∀ h : i < E.length, ∀ t : Fin m, a i = some t →
      (E[i]'h).comap U.ι = (coordinateSubspaceIdeal k m {t}).comap c)
def HasSimpleNormalCrossings {X : Scheme.{u}} {k : Type u} [Field k] (p : X ⟶ Spec (CommRingCat.of k))
    (E : List X.IdealSheafData) : Prop :=
  (∀ D ∈ E, IsSmoothDivisor p D) ∧ ∀ x : X, HasSimpleNormalCrossingsAt p E x
def HasSimpleNormalCrossingsWith {X : Scheme.{u}} {k : Type u} [Field k] (p : X ⟶ Spec (CommRingCat.of k))
    (Z : X.IdealSheafData) (E : List X.IdealSheafData) : Prop :=
  ∀ x ∈ Z.support,
    ∃ (U : X.Opens) (_ : x ∈ U) (m : ℕ) (c : U.toScheme ⟶ affineSpaceOverField k m)
      (_ : c ≫ (affineSpaceOverField k m ↘ Spec (CommRingCat.of k)) = U.ι ≫ p) (_ : Etale c)
      (a : ℕ → Option (Fin m)) (S : Finset (Fin m)),
      (∀ i < E.length, ∀ j < E.length, ∀ t : Fin m, a i = some t → a j = some t → i = j) ∧
      (∀ i, ∀ h : i < E.length, a i = none → (E[i]'h).comap U.ι = ⊤) ∧
      (∀ i, ∀ h : i < E.length, ∀ t : Fin m, a i = some t →
        (E[i]'h).comap U.ι = (coordinateSubspaceIdeal k m {t}).comap c) ∧
      Z.comap U.ι = (coordinateSubspaceIdeal k m S).comap c
def strictTransform {X' X : Scheme.{u}} (f : X' ⟶ X) (Z J : X.IdealSheafData) : X'.IdealSheafData :=
  (((J.comap f).subschemeι ⁻¹ᵁ (Z.comap f).support.compl).ι ≫ (J.comap f).subschemeι).ker
def BlowupSequence.exceptionalProduct {X : Scheme.{u}} (s : BlowupSequence X) : ∀ i : ℕ, (s.obj i).IdealSheafData
  | 0 => ⊤
  | i + 1 => (s.exceptionalProduct i).comap (s.blowupMap i) * (s.center i).comap (s.blowupMap i)
def IsPrincipalizingSequence {X : Scheme.{u}} {k : Type u} [Field k] (p : X ⟶ Spec (CommRingCat.of k))
    (I : X.IdealSheafData) (E : List X.IdealSheafData) (s : BlowupSequence X) : Prop :=
  ∃ (ideal : ∀ i : ℕ, (s.obj i).IdealSheafData) (boundary : ∀ i : ℕ, List (s.obj i).IdealSheafData),
    ideal 0 = I.comap (s.structMap 0) ∧
    boundary 0 = E.map (fun D => D.comap (s.structMap 0)) ∧
    (∀ i, i < s.length → Smooth ((s.center i).subschemeι ≫ s.structMap i ≫ p)) ∧
    (∀ i, i < s.length → HasSimpleNormalCrossingsWith (s.structMap i ≫ p) (s.center i) (boundary i)) ∧
    (∀ i, i < s.length → ideal i ≤ s.center i) ∧
    (∀ i, i < s.length →
      (s.center i).comap (s.blowupMap i) * ideal (i + 1) = (ideal i).comap (s.blowupMap i)) ∧
    (∀ i, i < s.length → boundary (i + 1) =
      (boundary i).map (strictTransform (s.blowupMap i) (s.center i)) ++ [(s.center i).comap (s.blowupMap i)]) ∧
    ideal s.length = ⊤ ∧
    I.comap s.topMap = s.exceptionalProduct s.length ∧
    (∀ i, i ≤ s.length → Smooth (s.structMap i ≫ p)) ∧
    (∀ i, i ≤ s.length → HasSimpleNormalCrossings (s.structMap i ≫ p) (boundary i))
abbrev PrincipalizationRuleCharZero : Type (u + 1) :=
  ∀ (k : Type u) [Field k] [CharZero k] (X : Scheme.{u}) (p : X ⟶ Spec (CommRingCat.of k))
    [Smooth p] [LocallyOfFiniteType p] [QuasiCompact p] (I : X.IdealSheafData), IsNonzeroOnComponents I →
      ∀ E : List X.IdealSheafData, HasSimpleNormalCrossings p E → BlowupSequence X
def IsPrincipalizationRuleCharZero (R : PrincipalizationRuleCharZero.{u}) : Prop :=
  ∀ (k : Type u) [Field k] [CharZero k] (X : Scheme.{u}) (p : X ⟶ Spec (CommRingCat.of k))
    [Smooth p] [LocallyOfFiniteType p] [QuasiCompact p]
    (I : X.IdealSheafData) (hI : IsNonzeroOnComponents I) (E : List X.IdealSheafData)
    (hE : HasSimpleNormalCrossings p E),
    IsPrincipalizingSequence p I E (R k X p I hI E hE)
def IsSmoothFunctorialPrincipalizationRule (R : PrincipalizationRuleCharZero.{u}) : Prop :=
  ∀ (k : Type u) [Field k] [CharZero k] (X : Scheme.{u}) (p : X ⟶ Spec (CommRingCat.of k))
    [Smooth p] [LocallyOfFiniteType p] [QuasiCompact p]
    (I : X.IdealSheafData) (hI : IsNonzeroOnComponents I) (E : List X.IdealSheafData)
    (hE : HasSimpleNormalCrossings p E)
    (X' : Scheme.{u}) (p' : X' ⟶ Spec (CommRingCat.of k)) [Smooth p'] [LocallyOfFiniteType p'] [QuasiCompact p']
    (φ : X' ⟶ X) [Smooth φ], φ ≫ p = p' →
    ∀ (hI' : IsNonzeroOnComponents (I.comap φ)) (hE' : HasSimpleNormalCrossings p' (E.map fun D => D.comap φ)),
      IsPullbackSequence φ (R k X' p' (I.comap φ) hI' (E.map fun D => D.comap φ) hE') (R k X p I hI E hE)
def IsFieldExtensionFunctorialPrincipalizationRule (R : PrincipalizationRuleCharZero.{u}) : Prop :=
  ∀ (k : Type u) [Field k] [CharZero k] (X : Scheme.{u}) (p : X ⟶ Spec (CommRingCat.of k))
    [Smooth p] [LocallyOfFiniteType p] [QuasiCompact p]
    (I : X.IdealSheafData) (hI : IsNonzeroOnComponents I) (E : List X.IdealSheafData)
    (hE : HasSimpleNormalCrossings p E) (K : Type u) [Field K] [CharZero K] [Algebra k K]
    (hI' : IsNonzeroOnComponents (I.comap (fieldBaseChangeProj p K)))
    (hE' : HasSimpleNormalCrossings (fieldBaseChangeStructMap p K)
      (E.map fun D => D.comap (fieldBaseChangeProj p K))),
    IsPullbackSequence (fieldBaseChangeProj p K)
      (R K (fieldBaseChange p K) (fieldBaseChangeStructMap p K) (I.comap (fieldBaseChangeProj p K)) hI'
        (E.map fun D => D.comap (fieldBaseChangeProj p K)) hE')
      (R k X p I hI E hE)
def FunctorialPrincipalizationCharZero : Prop :=
  ∃ R : PrincipalizationRuleCharZero.{u},
    IsPrincipalizationRuleCharZero R ∧ IsSmoothFunctorialPrincipalizationRule R ∧
      IsFieldExtensionFunctorialPrincipalizationRule R
end
end FunctorialResolution


