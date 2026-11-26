-- Prove2me | Definitions.Def_Operator_Crouzeix_CompactThickeningApprox
-- name    : Operator_Crouzeix_CompactThickeningApprox
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T12:31:49.795422+00:00
-- url     : https://prove2.me/theorems/82b1b0ea-17b7-4c78-892d-8a1b2a5d6ca0
-- title:
--   Compact Thickening Approx
-- statement:
--   Definitions and structural lemmas for Compact Thickening Approx, from Ezzeri Esa (savarin/lean-operator-theory; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Crouzeix-Palencia theorem, von Neumann inequality, and unitary power dilation development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/CompactThickeningApprox.lean

import Definitions.Def_Operator_Crouzeix_SmoothApprox
set_option autoImplicit false
open Metric Set
noncomputable def compactThickeningApprox (K : Set ℂ) (n : ℕ) : Set ℂ :=
  Metric.cthickening (smoothApproxRadius n) K


