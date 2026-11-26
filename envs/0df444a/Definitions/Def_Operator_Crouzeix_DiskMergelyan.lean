-- Prove2me | Definitions.Def_Operator_Crouzeix_DiskMergelyan
-- name    : Operator_Crouzeix_DiskMergelyan
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T13:58:18.026293+00:00
-- url     : https://prove2.me/theorems/13ec0e71-a778-4f7f-8fdd-61fdb5d20364
-- title:
--   Disk Mergelyan
-- statement:
--   Definitions and structural lemmas for Disk Mergelyan, from Ezzeri Esa (savarin/lean-operator-theory; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Crouzeix-Palencia theorem, von Neumann inequality, and unitary power dilation development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/DiskMergelyan.lean

import Definitions.Def_Operator_Crouzeix_SmoothJordanExhaustion
import Mathlib.Topology.UniformSpace.UniformConvergenceTopology
set_option autoImplicit false
open Complex Filter Metric Set
open scoped Topology
noncomputable def formalPartialSumPolynomial
    (p : FormalMultilinearSeries ℂ ℂ ℂ) (n : ℕ) : Polynomial ℂ :=
  ∑ k ∈ Finset.range n,
    Polynomial.C (p k (fun _ => 1)) * Polynomial.X ^ k
noncomputable def radialFactor (n : ℕ) : ℝ :=
  (n : ℝ) / ((n : ℝ) + 1)
noncomputable def radialMap (c : ℂ) (n : ℕ) (z : ℂ) : ℂ :=
  c + (radialFactor n : ℂ) * (z - c)
noncomputable def radialTaylorPolynomial
    (p : FormalMultilinearSeries ℂ ℂ ℂ) (n k : ℕ) (c : ℂ) : Polynomial ℂ :=
  (formalPartialSumPolynomial p k).comp
    (Polynomial.C (radialFactor n : ℂ) * (Polynomial.X - Polynomial.C c))


