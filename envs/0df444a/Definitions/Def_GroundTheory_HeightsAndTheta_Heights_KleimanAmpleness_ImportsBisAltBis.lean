-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_ImportsBisAltBis
-- name    : GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_ImportsBisAltBis
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T01:00:58.995602+00:00
-- url     : https://prove2.me/theorems/3bc5d57a-c8a4-46cd-b843-254034f2507f
-- title:
--   Imports Bis Alt Bis
-- statement:
--   Definitions and structural lemmas for Imports Bis Alt Bis, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/ImportsBisAltBis.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_EqZeroOrIsHomogeneousOfMemPolyPiece
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.Kleiman.TranslateEq
open MvPolynomial
def GradedCech.Statement : Prop :=
  ∀ (S : Type) [CommRing S] (N : ℕ),
    ∃ e : ∀ (M : Type) [AddCommGroup M] [Module (Poly S N) M] [Module S M] [IsScalarTower S (Poly S N) M]
        (G : IndefiniteRowSideFullHecke.Kleiman.GradedMod S N M) (i : ℕ) (c : ℤ),
        IndefiniteRowSideFullHecke.Kleiman.gradedH S N M G i c ≃ₗ[S] Kleiman.cohom (gradedEquiv S N M G) i c,
      (∀ (M M' : Type) [AddCommGroup M] [Module (Poly S N) M] [Module S M] [IsScalarTower S (Poly S N) M]
        [AddCommGroup M'] [Module (Poly S N) M'] [Module S M'] [IsScalarTower S (Poly S N) M']
        (G : IndefiniteRowSideFullHecke.Kleiman.GradedMod S N M) (G' : IndefiniteRowSideFullHecke.Kleiman.GradedMod S N M')
        (f : M →ₗ[Poly S N] M') (hf : IndefiniteRowSideFullHecke.Kleiman.IsGradedHom S N G G' f) (i : ℕ) (c : ℤ)
        (z : IndefiniteRowSideFullHecke.Kleiman.gradedH S N M G i c),
        e M' G' i c (IndefiniteRowSideFullHecke.Kleiman.gradedHmap S N hf i c z) =
          Kleiman.cohomMap (⟨f, fun c m hm => hf c m hm⟩ :
            Kleiman.GradedHom (gradedEquiv S N M G) (gradedEquiv S N M' G')) i c (e M G i c z)) ∧
      ∀ (M : Type) [AddCommGroup M] [Module (Poly S N) M] [Module S M] [IsScalarTower S (Poly S N) M]
        (G : IndefiniteRowSideFullHecke.Kleiman.GradedMod S N M) (c : ℤ) (m : M) (hm : m ∈ G.piece c)
        (z : IndefiniteRowSideFullHecke.Kleiman.gradedZ S N M G 0 c),
        (z : ∀ I, (IndefiniteRowSideFullHecke.Kleiman.gradedSys S N M G c).V I) = IndefiniteRowSideFullHecke.Kleiman.unitCochain S N M m →
        e M G 0 c (Submodule.Quotient.mk z) = Kleiman.toH0 (gradedEquiv S N M G) c ⟨m, hm⟩
end GroundTheory.Heights₂.Heights.Kleiman.TranslateEq


