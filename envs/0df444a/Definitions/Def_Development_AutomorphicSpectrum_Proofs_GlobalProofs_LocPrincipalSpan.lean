-- Prove2me | Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_LocPrincipalSpan
-- name    : Development_AutomorphicSpectrum_Proofs_GlobalProofs_LocPrincipalSpan
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T22:51:25.842883+00:00
-- url     : https://prove2.me/theorems/787d0089-492c-4267-9046-77489404c8d0
-- title:
--   Loc Principal Span
-- statement:
--   Definitions and structural lemmas for Loc Principal Span, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/LocPrincipalSpan.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace GlobalTheory.CompanionTheory.Hypotheses₂.CentreOver
def LocPrincipal {A : Type} [CommRing A] (I p : Ideal A) : Prop :=
  ∃ t f : A, t ∉ p ∧ f ∈ I ∧ f ≠ 0 ∧ ∀ g ∈ I, ∃ n : ℕ, t ^ n * g ∈ Ideal.span {f}
end GlobalTheory.CompanionTheory.Hypotheses₂.CentreOver


