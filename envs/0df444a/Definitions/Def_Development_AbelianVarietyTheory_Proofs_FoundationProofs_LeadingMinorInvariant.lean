-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_LeadingMinorInvariant
-- name    : Development_AbelianVarietyTheory_Proofs_FoundationProofs_LeadingMinorInvariant
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-25T03:09:02.081634+00:00
-- url     : https://prove2.me/theorems/ac6a1e29-f7c1-4c85-909b-7504678ae540
-- title:
--   Leading Minor Invariant
-- statement:
--   Definitions and structural lemmas for Leading Minor Invariant, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/LeadingMinorInvariant.lean

import Mathlib
import Definitions.Def_Formalism_FormalDegreeBessel_StatementG
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
noncomputable section
namespace GlobalTheory.LeadingMinorInv
open Formalism.QuantumDeterminants
def UpUni {n : ℕ} (U : Matrix (Fin n) (Fin n) ℂ) : Prop :=
  (∀ i j, j < i → U i j = 0) ∧ ∀ i, U i i = 1
def flagMat (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) :
    Matrix (Fin (2 * r + k + 1)) (Fin (r + 1)) ℂ := Matrix.of fun i a => fvec k r z a i
end GlobalTheory.LeadingMinorInv
namespace GlobalTheory
open Formalism.QuantumDeterminants LeadingMinorInv
end GlobalTheory


