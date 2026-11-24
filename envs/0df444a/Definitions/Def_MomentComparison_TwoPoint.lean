-- Prove2me | Definitions.Def_MomentComparison_TwoPoint
-- name    : MomentComparison_TwoPoint
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-24T10:11:22.286669+00:00
-- url     : https://prove2.me/theorems/2a67f90f-2713-43e7-a2e1-757768060142
-- title:
--   Two Point
-- statement:
--   Definitions and structural lemmas for Two Point, from XinyuanXie-hub (XinyuanXie-hub/MomentComparison; see pinned Apache-2.0 LICENSE)'s pinned Sharp two-sided bounds on the moment comparison constant Cstar development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/XinyuanXie-hub/MomentComparison/blob/30aae604e14c2e7a22e5eb3bcd3cfd6d02f61772/MomentComparison/TwoPoint.lean

module
public import Definitions.Def_MomentComparison_Lens
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Convex.Deriv
public import Mathlib.Analysis.Convex.SpecificFunctions.Pow
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
set_option autoImplicit true
@[expose] public section
public section
@[expose] section
open Filter Topology Set
namespace MomentComparison
def U (y x : ℝ) : ℝ := (1 + x) ^ 2 + y
def V (y x : ℝ) : ℝ := (1 - x) ^ 2 + y
noncomputable def S (s y x : ℝ) : ℝ :=
  (U y x ^ s + V y x ^ s) / 2
noncomputable def S₁ (s y x : ℝ) : ℝ :=
  s * (U y x ^ (s - 1) * (1 + x) - V y x ^ (s - 1) * (1 - x))
noncomputable def S₂ (s y x : ℝ) : ℝ :=
  s * (U y x ^ (s - 1) + V y x ^ (s - 1)) +
    2 * s * (s - 1) *
      (U y x ^ (s - 2) * (1 + x) ^ 2 + V y x ^ (s - 2) * (1 - x) ^ 2)
noncomputable def G (s y x : ℝ) : ℝ := S s y x ^ s⁻¹
noncomputable def G₁ (s y x : ℝ) : ℝ :=
  s⁻¹ * S s y x ^ (s⁻¹ - 1) * S₁ s y x
noncomputable def G₂ (s y x : ℝ) : ℝ :=
  s⁻¹ * S s y x ^ (s⁻¹ - 1) * S₂ s y x +
    s⁻¹ * (s⁻¹ - 1) * S s y x ^ (s⁻¹ - 2) * (S₁ s y x) ^ 2
end MomentComparison


