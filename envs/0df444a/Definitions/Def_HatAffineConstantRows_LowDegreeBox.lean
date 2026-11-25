-- Prove2me | Definitions.Def_HatAffineConstantRows_LowDegreeBox
-- name    : HatAffineConstantRows_LowDegreeBox
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T09:07:03.839994+00:00
-- url     : https://prove2.me/theorems/35aacd78-6fc6-42df-860c-05c7ed213782
-- title:
--   Low Degree Box
-- statement:
--   Definitions and structural lemmas for Low Degree Box, from insammael (insammael/one-sided-affine-hat-guessing; see pinned Apache-2.0 LICENSE)'s pinned One-sided affine obstructions in complete bipartite hat guessing development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/insammael/one-sided-affine-hat-guessing/blob/991721669233b41666e6f56b1471e58eb63d719e/Lean/HatAffineConstantRows/LowDegreeBox.lean

import Definitions.Def_HatAffineGenericCore_G2
set_option autoImplicit true
open scoped BigOperators
namespace HatAffineConstantRows
universe u
open Finset
open MvPolynomial
end HatAffineConstantRows


