-- Prove2me | Definitions.Def_Submission_ThreeSum_TernaryTaggedMinorSupport
-- name    : Submission_ThreeSum_TernaryTaggedMinorSupport
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T08:19:29.453203+00:00
-- url     : https://prove2.me/theorems/371c4349-1c90-4949-880f-f482960926fd
-- title:
--   Ternary Tagged Minor Support
-- statement:
--   Definitions and structural lemmas for Ternary Tagged Minor Support, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryTaggedMinorSupport.lean

import Definitions.Def_Submission_ThreeSum_TernaryPairedSupportConcrete
set_option autoImplicit false
noncomputable section
namespace ThreeSum.TernaryTaggedMinorSupport
open TernaryPairedSupport TernaryPairedPotential
open scoped BigOperators
attribute [local instance] Classical.propDecidable
variable {p Λ : ℕ} [Fact p.Prime]
variable {P W D : Type*} [Fintype P] [AddCommGroup W] [Module (ZMod p) W] [Fintype W] [DecidableEq D]
def retag (a b : Fin Λ) : (Fin Λ→ZMod p)→ₗ[ZMod p] ((Fin Λ→ZMod p)×(ZMod p×ZMod p)) where
  toFun v := (v,(v a,v b))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
end ThreeSum.TernaryTaggedMinorSupport


