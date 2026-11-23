-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CompletionUniversalLocalHom
-- name    : Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CompletionUniversalLocalHom
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T16:57:02.697946+00:00
-- url     : https://prove2.me/theorems/5ad25d0b-0461-4be0-a752-336ad4a2c487
-- title:
--   Completion Universal Local Hom
-- statement:
--   Definitions and structural lemmas for Completion Universal Local Hom, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/CompletionUniversalLocalHom.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_ProjectionSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsCplAtApprox
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing GlobalTheory.Pat
namespace GlobalTheory.Pat.CplMap
variable {R S S' : Type} [CommRing R] [CommRing S] [IsLocalRing S] [CommRing S'] [IsLocalRing S']
  {q : Ideal R} {φ : R →+* S} {ψ : R →+* S'}
variable [hq : q.IsPrime]
def IsVal (q : Ideal R) (φ : R →+* S) (ψ : R →+* S') (n : ℕ) (s : S)
    (t : S' ⧸ maximalIdeal S' ^ n) : Prop :=
  ∀ a b : R, b ∉ q → φ b * s - φ a ∈ maximalIdeal S ^ n →
    Ideal.Quotient.mk (maximalIdeal S' ^ n) (ψ b) * t = Ideal.Quotient.mk (maximalIdeal S' ^ n) (ψ a)
end GlobalTheory.Pat.CplMap
namespace GlobalTheory.Pat
open CplMap
end GlobalTheory.Pat


