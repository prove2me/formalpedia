-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_EqZeroOfEvalGridEqZeroOfTotalDegreeLe
-- name    : Development_AbelianVarietyTheory_Proofs_CovolumeBounds_EqZeroOfEvalGridEqZeroOfTotalDegreeLe
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T12:44:35.984396+00:00
-- url     : https://prove2.me/theorems/c0fdcce7-3180-4ebf-a0f3-f24693154eaa
-- title:
--   Eq Zero Of Eval Grid Eq Zero Of Total Degree Le
-- statement:
--   Definitions and structural lemmas for Eq Zero Of Eval Grid Eq Zero Of Total Degree Le, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/EqZeroOfEvalGridEqZeroOfTotalDegreeLe.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace GlobalTheory
open MvPolynomial
section Vanishing
variable {σ R : Type*} [Finite σ] [CommRing R] [IsDomain R] [CharZero R]
end Vanishing
section Span
variable {σ A K V : Type*} [Finite σ] [Field K] [CharZero K] [CommSemiring A] [Algebra A K]
  [AddCommGroup V] [Module K V]
end Span
section Combination
variable {ι κ V : Type*} [Fintype ι] [AddCommGroup V] {W : ι → Type*}
  [∀ j, AddCommGroup (W j)]
variable {K : Type*} [Field K] [CharZero K] [Module K V] [∀ j, Module K (W j)]
end Combination
end GlobalTheory


