-- Prove2me | Definitions.Def_TC433_LinearAlgebra_LinearEquiv_Basic_d2d629213e
-- name    : TC433_LinearAlgebra_LinearEquiv_Basic_d2d629213e
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T17:31:45.643893+00:00
-- url     : https://prove2.me/theorems/4e600df6-aa81-47c9-b96d-d2046b0be5e9
-- title:
--   TauCeti: LinearAlgebra / LinearEquiv / Basic
-- statement:
--   Compatibility port of the definitions and proved supporting lemmas in TauCeti.LinearAlgebra.LinearEquiv.Basic for the concrete CFSG catalog. This module does not assert the classification theorem.
-- source:
--   https://github.com/TauCetiProject/TauCeti/blob/6e0c6acab5f4c6f42e5f5bab9bd5e4e84f74c380/TauCeti/LinearAlgebra/LinearEquiv/Basic.lean

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.Submodule.Map

/-!
# Elementary linear-equivalence transport

Transport of submodule stability through an intertwining linear equivalence.
-/

public section
set_option backward.isDefEq.respectTransparency.types false

namespace LinearEquiv

/-- Transport stability of a mapped submodule through an intertwining linear equivalence. -/
theorem mem_of_preserves_map
    {R V W : Type*} [Semiring R]
    [AddCommMonoid V] [Module R V] [AddCommMonoid W] [Module R W]
    (e : V ≃ₗ[R] W) (p : Submodule R V) (q : Submodule R W)
    (hmap : p.map e.toLinearMap = q) (f : V → V) (g : W → W)
    (hcomm : ∀ x, e (f x) = g (e x))
    (hstable : ∀ {y}, y ∈ q → g y ∈ q)
    {x : V} (hx : x ∈ p) : f x ∈ p := by
  have hex : e x ∈ q := by
    rw [← hmap]
    exact Submodule.mem_map_of_mem hx
  have hfx := hstable hex
  rw [← hcomm x, ← hmap] at hfx
  simpa only [Submodule.mem_map_equiv, LinearEquiv.symm_apply_apply] using hfx

end LinearEquiv


