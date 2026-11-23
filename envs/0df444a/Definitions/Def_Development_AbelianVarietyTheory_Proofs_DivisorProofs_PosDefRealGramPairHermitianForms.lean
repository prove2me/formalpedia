-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PosDefRealGramPairHermitianForms
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_PosDefRealGramPairHermitianForms
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T16:17:22.586876+00:00
-- url     : https://prove2.me/theorems/2a5e7237-089f-42a9-8422-f7ef0e50f470
-- title:
--   Pos Def Real Gram Pair Hermitian Forms
-- statement:
--   Definitions and structural lemmas for Pos Def Real Gram Pair Hermitian Forms, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/PosDefRealGramPairHermitianForms.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
namespace GlobalTheory.HermGram
noncomputable def reForm {g : ℕ} (H : Matrix (Fin g) (Fin g) ℂ) :
    (Fin g → ℂ) →ₗ[ℝ] (Fin g → ℂ) →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (fun z w => (z ⬝ᵥ H *ᵥ star w).re)
    (by intro a b c; simp [add_dotProduct])
    (by intro c a b; simp [smul_dotProduct, Complex.smul_re])
    (by intro a b c; simp [star_add, mulVec_add, dotProduct_add])
    (by intro c a b
        have : star (c • b) = c • star b := by
          ext i; simp [Complex.conj_ofReal]
        rw [this, mulVec_smul, dotProduct_smul, Complex.smul_re])
end GlobalTheory.HermGram


