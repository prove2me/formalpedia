-- Prove2me | Definitions.Def_Operator_Crouzeix_SmoothSupportEnvelope
-- name    : Operator_Crouzeix_SmoothSupportEnvelope
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T14:02:56.507937+00:00
-- url     : https://prove2.me/theorems/a7213512-fe35-4144-9bdb-3a70a89aa485
-- title:
--   Smooth Support Envelope
-- statement:
--   Definitions and structural lemmas for Smooth Support Envelope, from Ezzeri Esa (savarin/lean-operator-theory; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Crouzeix-Palencia theorem, von Neumann inequality, and unitary power dilation development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SmoothSupportEnvelope.lean

import Definitions.Def_Operator_Crouzeix_PolytopeSoftSupportCurvature
set_option autoImplicit false
open Complex Metric Set
open scoped ComplexConjugate
noncomputable def smoothSupportDirectionalLinearMap (theta : ℝ) :
    ℂ →ₗ[ℝ] ℝ :=
  Real.cos theta • Complex.reCLM.toLinearMap +
    Real.sin theta • Complex.imCLM.toLinearMap
def smoothSupportClosedEnvelope (h : ℝ → ℝ) : Set ℂ :=
  {z | ∀ theta, polytopeDirectionalValue z theta ≤ h theta}
def smoothSupportOpenEnvelope (h : ℝ → ℝ) : Set ℂ :=
  interior (smoothSupportClosedEnvelope h)


