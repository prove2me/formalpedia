-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_HPInvEqForm
-- name    : Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_HPInvEqForm
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T12:51:39.866991+00:00
-- url     : https://prove2.me/theorems/8c62ae27-e029-4eca-a76e-851f5ad84129
-- title:
--   HPInv Eq Form
-- statement:
--   Definitions and structural lemmas for HPInv Eq Form, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/AutomorphicMembership/HPInvEqForm.lean

import Mathlib
import Definitions.Def_Formalism_DegreeFormula_Statement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Formalism.DegreeFormula Formalism.MJ Formalism.UG
open scoped ComplexOrder
namespace GlobalTheory.HodgeDomain
variable {p q : ℕ}
def jW (g : GL (Fin p ⊕ Fin q) ℂ) (z : Matrix (Fin p) (Fin q) ℂ) : Matrix (Fin p) (Fin p) ℂ :=
  (g : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ).toBlocks₁₁ -
    moeb (g : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) z * (g : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ).toBlocks₂₁
def autE (g : GL (Fin p ⊕ Fin q) ℂ) (z : Matrix (Fin p) (Fin q) ℂ) :
    Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ := fromBlocks (jW g z) 0 0 (kapQ g z)
def tanAct (g : GL (Fin p ⊕ Fin q) ℂ) (z ξ : Matrix (Fin p) (Fin q) ℂ) : Matrix (Fin p) (Fin q) ℂ :=
  jW g z * ξ * (kapQ g z)⁻¹
def blkMet (A : Matrix (Fin p) (Fin p) ℂ) (B : Matrix (Fin q) (Fin q) ℂ) :
    Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ := fromBlocks A 0 0 B
def hodge (c : ℝ) (z : Matrix (Fin p) (Fin q) ℂ) : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ :=
  blkMet ((c : ℂ) • (hP z)⁻¹) ((c : ℂ) • hQ z)
example (c : ℝ) : hodge c (0 : Matrix (Fin p) (Fin q) ℂ) = (c : ℂ) • 1 := by
  simp [hodge, blkMet, hP, hQ, ← fromBlocks_one, fromBlocks_smul]
end GlobalTheory.HodgeDomain


