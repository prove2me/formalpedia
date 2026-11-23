-- Prove2me | Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_Envelope
-- name    : Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_Envelope
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T04:19:52.969453+00:00
-- url     : https://prove2.me/theorems/1aec04b2-04ed-49a7-ad16-1f388bf17739
-- title:
--   Envelope
-- statement:
--   Definitions and structural lemmas for Envelope, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CrystallinePeriods/Envelope.lean

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_SpanNatCastLeComap
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Ideal
open scoped Nat
namespace Reformulated.AutPerF
section DP
variable {B : Type*} [CommRing B] [Algebra ℚ B]
def dp (m : ℕ) (x : B) : B := ((m ! : ℚ)⁻¹) • x ^ m
variable {A : Type*} [CommRing A] [Algebra A B]
def dpSpan (B : Type*) [CommRing B] [Algebra ℚ B] [Algebra A B] (ξ : A) (s : Set ℕ) :
    Submodule A B :=
  Submodule.span A ((fun m => dp m (algebraMap A B ξ)) '' s)
variable {ξ : A}
variable [IsDomain B] (h0 : algebraMap A B ξ ≠ 0)
  (hξ : ∀ a : A, algebraMap A B ξ ∣ algebraMap A B a → ξ ∣ a)
include h0 hξ
end DP
section Lattice
variable {A Q : Type*} [CommRing A] [CommRing Q]
def adicLift (p : ℕ) [IsAdicComplete (span {(p : Q)}) Q] (g : A →+* Q) :
    AdicCompletion (span {(p : A)}) A →+* Q :=
  (AdicCompletion.ofAlgEquiv (span {(p : Q)})).symm.toRingEquiv.toRingHom.comp
    (adicMap _ _ g (span_natCast_le_comap p g))
end Lattice
end Reformulated.AutPerF


