-- Prove2me | Definitions.Def_Operator_Crouzeix_SmoothSupportEnvelopeApproximation
-- name    : Operator_Crouzeix_SmoothSupportEnvelopeApproximation
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T14:04:36.164967+00:00
-- url     : https://prove2.me/theorems/330a8dfc-8e92-4de1-bc70-bbc0a9b1a4ed
-- title:
--   Smooth Support Envelope Approximation
-- statement:
--   Definitions and structural lemmas for Smooth Support Envelope Approximation, from Ezzeri Esa (savarin/lean-operator-theory; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Crouzeix-Palencia theorem, von Neumann inequality, and unitary power dilation development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SmoothSupportEnvelopeApproximation.lean

import Definitions.Def_Operator_Crouzeix_SmoothSupportEnvelope
import Mathlib.Analysis.InnerProductSpace.Projection.Minimal
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
set_option autoImplicit false
open Complex Metric Set
open scoped InnerProductSpace


