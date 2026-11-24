-- Prove2me | Definitions.Def_GaussianPerimeter_PrekopaLeindler
-- name    : GaussianPerimeter_PrekopaLeindler
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-24T10:08:23.874652+00:00
-- url     : https://prove2.me/theorems/86064a17-5809-4056-aa25-d9dec484d7f2
-- title:
--   Prekopa Leindler
-- statement:
--   Definitions and structural lemmas for Prekopa Leindler, from XinyuanXie-hub (XinyuanXie-hub/GaussianPerimeter; see pinned Apache-2.0 LICENSE)'s pinned Asymptotic lower bound for Gaussian perimeter of convex bodies development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/XinyuanXie-hub/GaussianPerimeter/blob/c54671095b3fdc672137addf46aa638c813db46a/GaussianPerimeter/PrekopaLeindler.lean

module
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Definitions.Def_GaussianPerimeter_PrekopaHelpers
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Integral.Lebesgue.Add
set_option autoImplicit true
@[expose] public section
public section
@[expose] section
namespace GaussianPerimeter.VolumeComparison
open MeasureTheory Set
open scoped Pointwise
def append {d : ℕ} (x : Fin d → ℝ) (t : Fin 1 → ℝ) : Fin (d + 1) → ℝ :=
  fun i ↦ if h : i.val < d then x ⟨i.val, h⟩ else t default
def fix {d : ℕ} (F : (Fin (d + 1) → ℝ) → ENNReal) (x : Fin d → ℝ) : (Fin 1 → ℝ) → ENNReal :=
  F ∘ (append x)
@[expose] def PLConditions (n : ℕ) (θ : ℝ) (f g h : (Fin n → ℝ) → ENNReal) : Prop :=
  0 < θ ∧ θ < 1 ∧
  Measurable f ∧ Measurable g ∧ Measurable h ∧
  (∀ x y, (f x)^(1-θ) * (g y)^θ ≤ h (x + y))
end GaussianPerimeter.VolumeComparison


