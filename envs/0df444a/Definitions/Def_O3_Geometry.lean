-- Prove2me | Definitions.Def_O3_Geometry
-- name    : O3_Geometry
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T13:49:39.173028+00:00
-- url     : https://prove2.me/theorems/56bde91f-8d38-4078-ba58-2c1d6cabbf09
-- title:
--   Geometry
-- statement:
--   Definitions and structural lemmas for Geometry, from Yuning Yang (yuningyang19/parameter_free_gradient_p; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Parameter-free gradient minimization in l_p geometry development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/yuningyang19/parameter_free_gradient_p/blob/f71215fa936fe01aff8a765c62b399e131df963b/O3/Geometry.lean

import Mathlib
set_option autoImplicit true
open scoped BigOperators
namespace O3
abbrev Point (d : ℕ) := Fin d → ℝ
def pairing {d : ℕ} (x y : Point d) : ℝ := ∑ i, x i * y i
noncomputable def conjugateExponent (p : ℝ) : ℝ := Real.conjExponent p
noncomputable def lpPower (p : ℝ) {d : ℕ} (x : Point d) : ℝ := ∑ i, |x i| ^ p
noncomputable def lpNorm (p : ℝ) {d : ℕ} (x : Point d) : ℝ := (lpPower p x) ^ (1 / p)
noncomputable def powerDualityMap (p : ℝ) {d : ℕ} (u : Point d) : Point d :=
  fun i ↦ |u i| ^ (p - 2) * u i
noncomputable def uniformRegularizer (p : ℝ) {d : ℕ} (c x : Point d) : ℝ :=
  (1 / p) * lpPower p (x - c)
noncomputable def dualityMap (p : ℝ) {d : ℕ} (u : Point d) : Point d :=
  if lpNorm p u = 0 then 0
  else fun i ↦ (lpNorm p u) ^ (2 - p) * (|u i| ^ (p - 2) * u i)
noncomputable def quadraticRegularizer (p : ℝ) {d : ℕ} (c x : Point d) : ℝ :=
  (1 / 2 : ℝ) * (lpNorm p (x - c)) ^ (2 : ℕ)
noncomputable def PUniformConvexityStatement : Prop :=
  ∀ (p : ℝ), 2 < p → ∀ (d : ℕ) (x y c : Point d),
    uniformRegularizer p c y ≥
      uniformRegularizer p c x + pairing (powerDualityMap p (x - c)) (y - x) +
        (2 ^ (2 - p) / p) * (lpNorm p (y - x)) ^ p
noncomputable def BelowGeometryStatement : Prop :=
  ∀ (p : ℝ), 1 < p → p ≤ 2 → ∀ (d : ℕ) (x y : Point d),
    quadraticRegularizer p 0 y ≥
      quadraticRegularizer p 0 x + pairing (dualityMap p x) (y - x) +
        ((p - 1) / 2) * (lpNorm p (y - x)) ^ (2 : ℕ)
end O3


