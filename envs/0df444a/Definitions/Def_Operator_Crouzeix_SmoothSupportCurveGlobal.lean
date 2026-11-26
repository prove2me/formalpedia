-- Prove2me | Definitions.Def_Operator_Crouzeix_SmoothSupportCurveGlobal
-- name    : Operator_Crouzeix_SmoothSupportCurveGlobal
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T14:06:24.110812+00:00
-- url     : https://prove2.me/theorems/97098e19-5fb3-4c2e-aa59-edecb502cca6
-- title:
--   Smooth Support Curve Global
-- statement:
--   Definitions and structural lemmas for Smooth Support Curve Global, from Ezzeri Esa (savarin/lean-operator-theory; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Crouzeix-Palencia theorem, von Neumann inequality, and unitary power dilation development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SmoothSupportCurveGlobal.lean

import Definitions.Def_Operator_Crouzeix_SmoothSupportCurve
import Definitions.Def_Operator_Crouzeix_SmoothSupportEnvelopeApproximation
set_option autoImplicit false
open Complex Metric Set
open scoped ContDiff


