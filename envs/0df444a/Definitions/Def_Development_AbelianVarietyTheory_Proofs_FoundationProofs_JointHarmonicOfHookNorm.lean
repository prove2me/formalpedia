-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_JointHarmonicOfHookNorm
-- name    : Development_AbelianVarietyTheory_Proofs_FoundationProofs_JointHarmonicOfHookNorm
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-24T22:18:28.854605+00:00
-- url     : https://prove2.me/theorems/b8c28fcc-75a1-4215-8aca-42b45973206d
-- title:
--   Joint Harmonic Of Hook Norm
-- statement:
--   Definitions and structural lemmas for Joint Harmonic Of Hook Norm, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/JointHarmonicOfHookNorm.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TorsionBlocks_LowerUnipotentMinors
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TorsionBlocks_BottomMinor
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.JointHarm
open MvPolynomial Matrix GlobalTheory.IndefiniteRowSideFullHecke.SubstitutionPolynomials
section Minors
variable {R : Type*} [CommRing R]
variable {n l : ℕ}
end Minors
variable {n p q : ℕ}
section Killed
end Killed
section Fock
open Formalism.E
variable {σ₁ σ₂ τ : Type} {f : σ₁ → τ} {g : σ₂ → τ}
end Fock
end GlobalTheory.JointHarm


