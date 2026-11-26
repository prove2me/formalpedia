-- Prove2me | Definitions.Def_Operator_Crouzeix_PolytopeSoftSupportCurvature
-- name    : Operator_Crouzeix_PolytopeSoftSupportCurvature
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T13:58:47.333473+00:00
-- url     : https://prove2.me/theorems/750d2b3e-99d3-59db-a956-93f9eafcadc8
-- title:
--   Polytope Soft Support Curvature
-- statement:
--   Definitions and structural lemmas for Polytope Soft Support Curvature, from Ezzeri Esa (savarin/lean-operator-theory; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Crouzeix-Palencia theorem, von Neumann inequality, and unitary power dilation development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/PolytopeSoftSupportCurvature.lean

import Definitions.Def_Operator_Crouzeix_PolytopeSoftSupport
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
set_option autoImplicit false
open Complex Set
open scoped ContDiff
noncomputable def polytopeDirectionalVelocity (z : ℂ) (theta : ℝ) : ℝ :=
  -z.re * Real.sin theta + z.im * Real.cos theta
noncomputable def polytopeSoftPartitionFirst
    (u : Finset ℂ) (delta theta : ℝ) : ℝ :=
  ∑ z ∈ u, Real.exp (polytopeDirectionalValue z theta / delta) *
    (polytopeDirectionalVelocity z theta / delta)
noncomputable def polytopeSoftPartitionSecond
    (u : Finset ℂ) (delta theta : ℝ) : ℝ :=
  ∑ z ∈ u, Real.exp (polytopeDirectionalValue z theta / delta) *
    ((polytopeDirectionalVelocity z theta / delta) ^ 2 -
      polytopeDirectionalValue z theta / delta)
noncomputable def polytopeSoftPartitionPositionMoment
    (u : Finset ℂ) (delta theta : ℝ) : ℝ :=
  ∑ z ∈ u, Real.exp (polytopeDirectionalValue z theta / delta) *
    (polytopeDirectionalValue z theta / delta)
noncomputable def polytopeSoftPartitionVelocitySqMoment
    (u : Finset ℂ) (delta theta : ℝ) : ℝ :=
  ∑ z ∈ u, Real.exp (polytopeDirectionalValue z theta / delta) *
    (polytopeDirectionalVelocity z theta / delta) ^ 2
noncomputable def polytopeSoftSupportFirst
    (u : Finset ℂ) (delta theta : ℝ) : ℝ :=
  delta * (polytopeSoftPartitionFirst u delta theta /
    polytopeSoftPartition u delta theta)
noncomputable def polytopeSoftSupportSecond
    (u : Finset ℂ) (delta theta : ℝ) : ℝ :=
  delta *
    ((polytopeSoftPartitionSecond u delta theta *
          polytopeSoftPartition u delta theta -
        polytopeSoftPartitionFirst u delta theta ^ 2) /
      polytopeSoftPartition u delta theta ^ 2)
noncomputable def polytopeRoundedSupport
    (u : Finset ℂ) (delta rho theta : ℝ) : ℝ :=
  polytopeSoftSupport u delta theta + rho


