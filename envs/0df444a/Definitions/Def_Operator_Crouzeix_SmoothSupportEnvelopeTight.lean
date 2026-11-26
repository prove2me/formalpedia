-- Prove2me | Definitions.Def_Operator_Crouzeix_SmoothSupportEnvelopeTight
-- name    : Operator_Crouzeix_SmoothSupportEnvelopeTight
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T14:05:50.515204+00:00
-- url     : https://prove2.me/theorems/6d82c89d-4719-49c8-8142-33814ab97767
-- title:
--   Smooth Support Envelope Tight
-- statement:
--   Definitions and structural lemmas for Smooth Support Envelope Tight, from Ezzeri Esa (savarin/lean-operator-theory; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Crouzeix-Palencia theorem, von Neumann inequality, and unitary power dilation development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SmoothSupportEnvelopeTight.lean

import Definitions.Def_Operator_Crouzeix_SmoothSupportEnvelopeApproximation
import Definitions.Def_Operator_Crouzeix_SmoothSupportCurve
set_option autoImplicit false
open Complex Metric Set
open scoped ContDiff


