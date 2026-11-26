-- Prove2me | Definitions.Def_Tablet_psiTilde
-- name    : Tablet_psiTilde
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T12:49:29.033805+00:00
-- url     : https://prove2.me/theorems/eef2dcd0-290d-4195-901b-94f8c2d69f18
-- title:
--   psi Tilde
-- statement:
--   Definitions and structural lemmas for psi Tilde, from Daniel Spector (Inspectordaniel/metric-surgery-lean; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Atomic decomposition of one-dimensional metric currents without boundary development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Inspectordaniel/metric-surgery-lean/blob/91c2fc65884c9b284fdc6ba4071aa63c12ded471/Tablet/psiTilde.lean

import Definitions.Def_Tablet_Curve
import Mathlib.Topology.MetricSpace.HausdorffDistance
set_option autoImplicit false
noncomputable def psiTilde {E : Type*} [MetricSpace E] (m : ℕ) (Q : Finset E) (ε C : ℝ)
    (γ : Curve E) : ℝ :=
-- BODY
  2 * C ^ 2 * γ.len ^ 2 / m
    + C * γ.len / m * ∑ i ∈ Finset.Icc 1 m,
        min (2 * C) (ε + 2 * C * Metric.infDist (γ.toFun (i * γ.len / m)) (Q : Set E))


