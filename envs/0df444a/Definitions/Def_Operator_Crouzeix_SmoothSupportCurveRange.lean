-- Prove2me | Definitions.Def_Operator_Crouzeix_SmoothSupportCurveRange
-- name    : Operator_Crouzeix_SmoothSupportCurveRange
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T14:07:15.764848+00:00
-- url     : https://prove2.me/theorems/217e8056-1eb4-595d-89af-db86e8b5504f
-- title:
--   Smooth Support Curve Range
-- statement:
--   Definitions and structural lemmas for Smooth Support Curve Range, from Ezzeri Esa (savarin/lean-operator-theory; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Crouzeix-Palencia theorem, von Neumann inequality, and unitary power dilation development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SmoothSupportCurveRange.lean

import Definitions.Def_Operator_Crouzeix_SmoothSupportCurveGlobal
set_option autoImplicit false
open Complex Metric Set
open scoped ContDiff


