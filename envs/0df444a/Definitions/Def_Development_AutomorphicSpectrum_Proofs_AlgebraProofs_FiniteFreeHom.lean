-- Prove2me | Definitions.Def_Development_AutomorphicSpectrum_Proofs_AlgebraProofs_FiniteFreeHom
-- name    : Development_AutomorphicSpectrum_Proofs_AlgebraProofs_FiniteFreeHom
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T16:34:26.883627+00:00
-- url     : https://prove2.me/theorems/704ec288-ce52-4af0-af1f-22c8826778fd
-- title:
--   Finite Free Hom
-- statement:
--   Definitions and structural lemmas for Finite Free Hom, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/AlgebraProofs/FiniteFreeHom.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.CompanionTheory.FreeQuotProof.Nbhd
def FiniteFreeHom {A B : Type} [CommRing A] [CommRing B] (φ : A →+* B) : Prop :=
  letI := φ.toAlgebra
  Module.Free A B ∧ Module.Finite A B
end GlobalTheory.CompanionTheory.FreeQuotProof.Nbhd


