-- Prove2me | Definitions.Def_Operator_Crouzeix_SmoothJordanCompact
-- name    : Operator_Crouzeix_SmoothJordanCompact
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T13:18:56.586041+00:00
-- url     : https://prove2.me/theorems/b090e341-6000-4fb3-ac45-b294d7916f70
-- title:
--   Smooth Jordan Compact
-- statement:
--   Definitions and structural lemmas for Smooth Jordan Compact, from Ezzeri Esa (savarin/lean-operator-theory; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Crouzeix-Palencia theorem, von Neumann inequality, and unitary power dilation development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SmoothJordanCompact.lean

import Definitions.Def_Operator_Crouzeix_ScalarCauchyKernelWinding
import Definitions.Def_Operator_Crouzeix_ScalarCompanionRadial
set_option autoImplicit false
open Complex Metric Set


