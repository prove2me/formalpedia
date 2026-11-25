-- Prove2me | Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_KrullDimQuotientEqTrdegSucc
-- name    : Development_AutomorphicSpectrum_Proofs_BlockDecomposition_KrullDimQuotientEqTrdegSucc
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-25T02:24:14.34154+00:00
-- url     : https://prove2.me/theorems/bd6f04c7-c9ae-50de-8709-c1f0d7daa5f9
-- title:
--   Krull Dim Quotient Eq Trdeg Succ
-- statement:
--   Definitions and structural lemmas for Krull Dim Quotient Eq Trdeg Succ, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/KrullDimQuotientEqTrdegSucc.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_PIntDomainDim
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry
namespace GlobalTheory.CompanionTheory.DimChart
theorem isIso_residueFieldMap {X Y : Scheme.{0}} (j : X ⟶ Y) [IsOpenImmersion j] (x : X) :
    IsIso (j.residueFieldMap x) := by
  refine (ConcreteCategory.isIso_iff_bijective _).mpr ⟨(j.residueFieldMap x).hom.injective, ?_⟩
  intro a
  obtain ⟨b, rfl⟩ := X.residue_surjective x a
  obtain ⟨c, rfl⟩ := j.stalkMap_surjective x b
  refine ⟨Y.residue _ c, ?_⟩
  rw [← CommRingCat.comp_apply, Scheme.residue_residueFieldMap]
  rfl
noncomputable def residueFieldEquiv {Y : Scheme.{0}} {B : Type} [CommRing B] (j : Spec (.of B) ⟶ Y)
    [IsOpenImmersion j] (q : PrimeSpectrum B) :
    Y.residueField (j q) ≃+* q.asIdeal.ResidueField :=
  haveI := isIso_residueFieldMap j q
  (asIso (j.residueFieldMap q) ≪≫ Scheme.Spec.residueFieldIso (.of B) q).commRingCatIsoToRingEquiv
end GlobalTheory.CompanionTheory.DimChart


