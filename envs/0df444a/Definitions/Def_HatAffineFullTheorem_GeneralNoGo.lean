-- Prove2me | Definitions.Def_HatAffineFullTheorem_GeneralNoGo
-- name    : HatAffineFullTheorem_GeneralNoGo
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T09:10:22.799567+00:00
-- url     : https://prove2.me/theorems/944ecfc2-2217-465d-906c-17537de23ca5
-- title:
--   General No Go
-- statement:
--   Definitions and structural lemmas for General No Go, from insammael (insammael/one-sided-affine-hat-guessing; see pinned Apache-2.0 LICENSE)'s pinned One-sided affine obstructions in complete bipartite hat guessing development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/insammael/one-sided-affine-hat-guessing/blob/991721669233b41666e6f56b1471e58eb63d719e/Lean/HatAffineFullTheorem/GeneralNoGo.lean

import Definitions.Def_HatAffineFullTheorem_LeadingClassification
import Definitions.Def_HatAffineOffsets_TypeI
import Definitions.Def_HatAffineOffsets_TypeII
set_option autoImplicit true
open scoped BigOperators
namespace HatAffineFullTheorem
universe u
noncomputable local instance _p2m_local_instance_f43eda1e4a_11 (p : Prop) : Decidable p :=
  Classical.propDecidable p
end HatAffineFullTheorem


