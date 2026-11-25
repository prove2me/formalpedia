-- Prove2me | Definitions.Def_HatAffineFullTheorem_LeadingClassification
-- name    : HatAffineFullTheorem_LeadingClassification
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T09:08:41.528796+00:00
-- url     : https://prove2.me/theorems/8408464c-49e5-5a31-898c-cb96fe393ecb
-- title:
--   Leading Classification
-- statement:
--   Definitions and structural lemmas for Leading Classification, from insammael (insammael/one-sided-affine-hat-guessing; see pinned Apache-2.0 LICENSE)'s pinned One-sided affine obstructions in complete bipartite hat guessing development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/insammael/one-sided-affine-hat-guessing/blob/991721669233b41666e6f56b1471e58eb63d719e/Lean/HatAffineFullTheorem/LeadingClassification.lean

import Definitions.Def_HatAffineGenericCore_G2
import Definitions.Def_HatAffineFactorAlignment_FactorAlignment
import Definitions.Def_HatAffineConstantRows_ConstantRows
set_option autoImplicit true
open scoped BigOperators
namespace HatAffineFullTheorem
universe u
open Finset
open MvPolynomial
open HatAffineGenericCore
end HatAffineFullTheorem


