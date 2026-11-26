-- Prove2me | Definitions.Def_Operator_Crouzeix_BoundaryApproximation
-- name    : Operator_Crouzeix_BoundaryApproximation
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T12:50:56.463478+00:00
-- url     : https://prove2.me/theorems/e6070794-b3dc-41fd-bea3-6c76028ede8a
-- title:
--   Boundary Approximation
-- statement:
--   Definitions and structural lemmas for Boundary Approximation, from Ezzeri Esa (savarin/lean-operator-theory; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Crouzeix-Palencia theorem, von Neumann inequality, and unitary power dilation development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/BoundaryApproximation.lean

import Definitions.Def_Operator_Crouzeix_ApproximationSupNorm
import Definitions.Def_Operator_Crouzeix_BoundaryMaximum
import Definitions.Def_Operator_Crouzeix_CompactThickeningApprox
set_option autoImplicit false
open Filter Polynomial Set


