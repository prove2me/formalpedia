-- Prove2me | Definitions.Def_Operator_Crouzeix_BoundaryMaximum
-- name    : Operator_Crouzeix_BoundaryMaximum
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T12:50:16.131771+00:00
-- url     : https://prove2.me/theorems/ca608155-c489-57a6-9adf-cdb19fe41d40
-- title:
--   Boundary Maximum
-- statement:
--   Definitions and structural lemmas for Boundary Maximum, from Ezzeri Esa (savarin/lean-operator-theory; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Crouzeix-Palencia theorem, von Neumann inequality, and unitary power dilation development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/BoundaryMaximum.lean

import Mathlib.Analysis.Complex.AbsMax
import Definitions.Def_Operator_Crouzeix_ApproximationSupNorm
import Definitions.Def_Operator_Crouzeix_GeneralSymmetrized
set_option autoImplicit false
open Complex Polynomial Set


