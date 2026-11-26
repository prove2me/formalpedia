-- Prove2me | Definitions.Def_Tablet_psi
-- name    : Tablet_psi
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T12:47:57.898794+00:00
-- url     : https://prove2.me/theorems/81a6051e-db49-499c-b4e7-486cc951e8ab
-- title:
--   psi
-- statement:
--   Definitions and structural lemmas for psi, from Daniel Spector (Inspectordaniel/metric-surgery-lean; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Atomic decomposition of one-dimensional metric currents without boundary development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Inspectordaniel/metric-surgery-lean/blob/91c2fc65884c9b284fdc6ba4071aa63c12ded471/Tablet/psi.lean

import Definitions.Def_Tablet_Curve
import Mathlib.Topology.MetricSpace.HausdorffDistance
set_option autoImplicit false
noncomputable def psi {E : Type*} [MetricSpace E] (m : ℕ) (Q : Finset E) (ε C : ℝ)
    (γ : Curve E) : ℝ :=
-- BODY
  C * (∑ i ∈ Finset.Icc 1 m,
        min (2 * C * γ.len / m)
          (2 * ε + 2 * C * (Metric.infDist (γ.toFun (i * γ.len / m)) (Q : Set E)
                          + Metric.infDist (γ.toFun ((i - 1) * γ.len / m)) (Q : Set E))))
    + 2 * C ^ 2 * γ.len ^ 2 / m


