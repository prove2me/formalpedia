-- Prove2me | Definitions.Def_Tablet_IsDeltaEpsN
-- name    : Tablet_IsDeltaEpsN
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T12:59:23.250881+00:00
-- url     : https://prove2.me/theorems/b18a030c-ae1b-4b47-bc93-b52fb93ee6eb
-- title:
--   Is Delta Eps N
-- statement:
--   Definitions and structural lemmas for Is Delta Eps N, from Daniel Spector (Inspectordaniel/metric-surgery-lean; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Atomic decomposition of one-dimensional metric currents without boundary development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Inspectordaniel/metric-surgery-lean/blob/91c2fc65884c9b284fdc6ba4071aa63c12ded471/Tablet/IsDeltaEpsN.lean

import Definitions.Def_Tablet_IsGeodesicResolution
import Definitions.Def_Tablet_IsClosedCurve
set_option autoImplicit false
open Set
def IsDeltaEpsN {E : Type*} [MetricSpace E] (γ : Curve E) (δ ε : ℝ) (n : ℕ) : Prop :=
-- BODY
  ∃ k : ℕ, ∃ s : ℕ → ℝ, IsGeodesicResolution γ k s ∧
    (∀ t t' : ℝ, 0 ≤ t → t ≤ t' → t' ≤ γ.len → t' - t ≤ 2 * ε⁻¹ * δ →
      ((Finset.Icc 1 k).filter
        (fun j => t ≤ s (j - 1) ∧ s j ≤ t' ∧ s j - s (j - 1) < δ)).card ≤ n) ∧
    (IsClosedCurve γ → ∀ t t' : ℝ, 0 ≤ t' → t' < t → t ≤ γ.len →
      (γ.len - t) + t' ≤ 2 * ε⁻¹ * δ →
      ((Finset.Icc 1 k).filter
        (fun j => (t ≤ s (j - 1) ∨ s j ≤ t') ∧ s j - s (j - 1) < δ)).card ≤ n)


