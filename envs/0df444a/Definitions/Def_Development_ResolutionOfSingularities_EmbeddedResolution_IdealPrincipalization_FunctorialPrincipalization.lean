-- Prove2me | Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IdealPrincipalization_FunctorialPrincipalization
-- name    : Development_ResolutionOfSingularities_EmbeddedResolution_IdealPrincipalization_FunctorialPrincipalization
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:15:39.476314+00:00
-- url     : https://prove2.me/theorems/58f19b58-16a5-442b-ad97-e4f3950392f0
-- title:
--   Functorial Principalization
-- statement:
--   Definitions and structural lemmas for Functorial Principalization, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/IdealPrincipalization/FunctorialPrincipalization.lean

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IteratedBlowups_BlowupSequenceRelations
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_ConstantCodimension
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_StrictNormalCrossings
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IdealPrincipalization_MarkedBlowupSequence_IdealBlowupSequence
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionOfSingularities
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
noncomputable section
namespace FunctorialResolution.EmbeddedResolution
abbrev PrincipalizationAlgorithm : Type (u + 1) :=
  ∀ (k : Type u) [Field k] [CharZero k] (X : Scheme.{u})
    (p : X ⟶ Spec (CommRingCat.of k))
    [AlgebraicGeometry.Smooth p] [AlgebraicGeometry.LocallyOfFiniteType p]
    [AlgebraicGeometry.QuasiCompact p]
    (I : X.IdealSheafData), NonzeroOnComponents I →
      ∀ E : List X.IdealSheafData, InStrictNormalCrossingPosition p E → IdealBlowupSequence p I E
abbrev specMapOfFieldHom (k K : Type u) [Field k] [Field K] (f : k →+* K) :
    Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of k) :=
  Spec.map (CommRingCat.ofHom f)
instance instSurjectiveSpecMapOfFieldHom (k K : Type u) [Field k] [Field K] (f : k →+* K) :
    Surjective (specMapOfFieldHom k K f) := by
  have hk : Subsingleton (PrimeSpectrum k) := by
    refine ⟨fun x y => ?_⟩
    have hx : x.asIdeal = ⊥ := x.asIdeal.eq_bot_or_top.resolve_right x.isPrime.ne_top
    have hy : y.asIdeal = ⊥ := y.asIdeal.eq_bot_or_top.resolve_right y.isPrime.ne_top
    exact PrimeSpectrum.ext (hx.trans hy.symm)
  obtain ⟨x⟩ : Nonempty (PrimeSpectrum K) := inferInstance
  refine ⟨fun y => ⟨x, ?_⟩⟩
  exact Subsingleton.elim (α := PrimeSpectrum k) _ _
instance instFlatSpecMapOfFieldHom (k K : Type u) [Field k] [Field K] (f : k →+* K) :
    Flat (specMapOfFieldHom k K f) := by
  show Flat (Spec.map (CommRingCat.ofHom f))
  let _inst : Algebra k K := f.toAlgebra
  have hflat : Module.Flat k K := inferInstance
  have hf : RingHom.Flat (CommRingCat.ofHom f).hom := hflat
  exact HasRingHomProperty.Spec_iff.mpr hf
structure IsFunctorialPrincipalization (A : PrincipalizationAlgorithm.{u}) : Prop where
  pushforward :
    ∀ (k : Type u) [Field k] [CharZero k] (S X : Scheme.{u})
      (pS : S ⟶ Spec (CommRingCat.of k)) (p : X ⟶ Spec (CommRingCat.of k))
      [AlgebraicGeometry.Smooth pS] [AlgebraicGeometry.LocallyOfFiniteType pS]
      [AlgebraicGeometry.QuasiCompact pS]
      [AlgebraicGeometry.Smooth p] [AlgebraicGeometry.LocallyOfFiniteType p]
      [AlgebraicGeometry.QuasiCompact p]
      (j : S ⟶ X) [IsClosedImmersion j] (_ : j ≫ p = pS)
      (c : ℕ) (_ : 1 ≤ c) (_ : HasEtaleCoordCodim p j c)
      (I : S.IdealSheafData) (hI : NonzeroOnComponents I)
      (hIX : NonzeroOnComponents (imageIdealSheaf j I))
      (hES : InStrictNormalCrossingPosition pS ([] : List S.IdealSheafData))
      (hEX : InStrictNormalCrossingPosition p ([] : List X.IdealSheafData)),
      IsPushforwardBlowupSeq j (A k S pS I hI [] hES).toSequenceOfBlowups
        (A k X p (imageIdealSheaf j I) hIX [] hEX).toSequenceOfBlowups
  base_change :
    ∀ (k : Type u) [Field k] [CharZero k] (X : Scheme.{u})
      (p : X ⟶ Spec (CommRingCat.of k))
      [AlgebraicGeometry.Smooth p] [AlgebraicGeometry.LocallyOfFiniteType p]
      [AlgebraicGeometry.QuasiCompact p]
      (I : X.IdealSheafData) (hI : NonzeroOnComponents I)
      (E : List X.IdealSheafData) (hE : InStrictNormalCrossingPosition p E)
      (K : Type u) [Field K] [CharZero K] (f : k →+* K)
      [AlgebraicGeometry.Smooth (pullback.snd p (specMapOfFieldHom k K f))]
      [AlgebraicGeometry.LocallyOfFiniteType (pullback.snd p (specMapOfFieldHom k K f))]
      [AlgebraicGeometry.QuasiCompact (pullback.snd p (specMapOfFieldHom k K f))]
      (hI' : NonzeroOnComponents (I.comap (pullback.fst p (specMapOfFieldHom k K f))))
      (hE' : InStrictNormalCrossingPosition (pullback.snd p (specMapOfFieldHom k K f))
        (E.map fun D => D.comap (pullback.fst p (specMapOfFieldHom k K f)))),
      IsPullbackBlowupSequence (pullback.fst p (specMapOfFieldHom k K f))
        (A K (pullback p (specMapOfFieldHom k K f)) (pullback.snd p (specMapOfFieldHom k K f))
          (I.comap (pullback.fst p (specMapOfFieldHom k K f))) hI'
          (E.map fun D => D.comap (pullback.fst p (specMapOfFieldHom k K f))) hE').toSequenceOfBlowups
        (A k X p I hI E hE).toSequenceOfBlowups
  base_change_strict :
    ∀ (k : Type u) [Field k] [CharZero k] (X : Scheme.{u})
      (p : X ⟶ Spec (CommRingCat.of k))
      [AlgebraicGeometry.Smooth p] [AlgebraicGeometry.LocallyOfFiniteType p]
      [AlgebraicGeometry.QuasiCompact p]
      (I : X.IdealSheafData) (hI : NonzeroOnComponents I)
      (E : List X.IdealSheafData) (hE : InStrictNormalCrossingPosition p E)
      (K : Type u) [Field K] [CharZero K] (f : k →+* K)
      [AlgebraicGeometry.Smooth (pullback.snd p (specMapOfFieldHom k K f))]
      [AlgebraicGeometry.LocallyOfFiniteType (pullback.snd p (specMapOfFieldHom k K f))]
      [AlgebraicGeometry.QuasiCompact (pullback.snd p (specMapOfFieldHom k K f))]
      (hI' : NonzeroOnComponents (I.comap (pullback.fst p (specMapOfFieldHom k K f))))
      (hE' : InStrictNormalCrossingPosition (pullback.snd p (specMapOfFieldHom k K f))
        (E.map fun D => D.comap (pullback.fst p (specMapOfFieldHom k K f)))),
      IsStrictPullbackBlowupSeq (pullback.fst p (specMapOfFieldHom k K f))
        (A K (pullback p (specMapOfFieldHom k K f)) (pullback.snd p (specMapOfFieldHom k K f))
          (I.comap (pullback.fst p (specMapOfFieldHom k K f))) hI'
          (E.map fun D => D.comap (pullback.fst p (specMapOfFieldHom k K f))) hE').toSequenceOfBlowups
        (A k X p I hI E hE).toSequenceOfBlowups
  lastIdeal_eq_top :
    ∀ (k : Type u) [Field k] [CharZero k] (X : Scheme.{u})
      (p : X ⟶ Spec (CommRingCat.of k))
      [AlgebraicGeometry.Smooth p] [AlgebraicGeometry.LocallyOfFiniteType p]
      [AlgebraicGeometry.QuasiCompact p]
      (I : X.IdealSheafData) (hI : NonzeroOnComponents I)
      (E : List X.IdealSheafData) (hE : InStrictNormalCrossingPosition p E),
      (A k X p I hI E hE).lastIdeal = ⊤
  smooth_pullback :
    ∀ (k : Type u) [Field k] [CharZero k] (X : Scheme.{u})
      (p : X ⟶ Spec (CommRingCat.of k))
      [AlgebraicGeometry.Smooth p] [AlgebraicGeometry.LocallyOfFiniteType p]
      [AlgebraicGeometry.QuasiCompact p]
      (I : X.IdealSheafData) (hI : NonzeroOnComponents I)
      (E : List X.IdealSheafData) (hE : InStrictNormalCrossingPosition p E)
      (X' : Scheme.{u}) (p' : X' ⟶ Spec (CommRingCat.of k))
      [AlgebraicGeometry.Smooth p'] [AlgebraicGeometry.LocallyOfFiniteType p']
      [AlgebraicGeometry.QuasiCompact p']
      (φ : X' ⟶ X) [AlgebraicGeometry.Smooth φ] (_ : φ ≫ p = p')
      (hI' : NonzeroOnComponents (I.comap φ))
      (hE' : InStrictNormalCrossingPosition p' (E.map fun D => D.comap φ)),
      IsPullbackBlowupSequence φ
        (A k X' p' (I.comap φ) hI' (E.map fun D => D.comap φ) hE').toSequenceOfBlowups
        (A k X p I hI E hE).toSequenceOfBlowups
  smooth_pullback_strict :
    ∀ (k : Type u) [Field k] [CharZero k] (X : Scheme.{u})
      (p : X ⟶ Spec (CommRingCat.of k))
      [AlgebraicGeometry.Smooth p] [AlgebraicGeometry.LocallyOfFiniteType p]
      [AlgebraicGeometry.QuasiCompact p]
      (I : X.IdealSheafData) (hI : NonzeroOnComponents I)
      (E : List X.IdealSheafData) (hE : InStrictNormalCrossingPosition p E)
      (X' : Scheme.{u}) (p' : X' ⟶ Spec (CommRingCat.of k))
      [AlgebraicGeometry.Smooth p'] [AlgebraicGeometry.LocallyOfFiniteType p']
      [AlgebraicGeometry.QuasiCompact p']
      (φ : X' ⟶ X) [AlgebraicGeometry.Smooth φ] [AlgebraicGeometry.Surjective φ]
      (_ : φ ≫ p = p')
      (hI' : NonzeroOnComponents (I.comap φ))
      (hE' : InStrictNormalCrossingPosition p' (E.map fun D => D.comap φ)),
      IsStrictPullbackBlowupSeq φ
        (A k X' p' (I.comap φ) hI' (E.map fun D => D.comap φ) hE').toSequenceOfBlowups
        (A k X p I hI E hE).toSequenceOfBlowups
end FunctorialResolution.EmbeddedResolution


