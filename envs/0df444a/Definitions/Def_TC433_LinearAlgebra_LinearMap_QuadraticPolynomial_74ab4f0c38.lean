-- Prove2me | Definitions.Def_TC433_LinearAlgebra_LinearMap_QuadraticPolynomial_74ab4f0c38
-- name    : TC433_LinearAlgebra_LinearMap_QuadraticPolynomial_74ab4f0c38
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T17:32:41.08762+00:00
-- url     : https://prove2.me/theorems/c78bad65-9602-4bd8-8ae9-34f174bb22e7
-- title:
--   TauCeti: LinearAlgebra / LinearMap / QuadraticPolynomial
-- statement:
--   Compatibility port of the definitions and proved supporting lemmas in TauCeti.LinearAlgebra.LinearMap.QuadraticPolynomial for the concrete CFSG catalog. This module does not assert the classification theorem.
-- source:
--   https://github.com/TauCetiProject/TauCeti/blob/6e0c6acab5f4c6f42e5f5bab9bd5e4e84f74c380/TauCeti/LinearAlgebra/LinearMap/QuadraticPolynomial.lean

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.LinearMap.Basic

/-!
# Quadratic expressions in modules

Three-term expressions of the form `x₀ + t • x₁ + t ^ 2 • x₂` occur in root-exponential actions.
The lemmas here preserve these formulas under coefficientwise equality and linear maps, allowing
root-exponential expressions to be compared after changing modules.
-/

public section
set_option backward.isDefEq.respectTransparency.types false

namespace TauCeti

/-- Equal coefficients give equal quadratic expressions. -/
theorem quadraticPolynomial_congr
    {A M : Type*} [Semiring A] [AddCommMonoid M] [Module A M]
    {x₀ x₁ x₂ y₀ y₁ y₂ : M} (t : A)
    (h₀ : x₀ = y₀) (h₁ : x₁ = y₁) (h₂ : x₂ = y₂) :
    x₀ + t • x₁ + t ^ 2 • x₂ = y₀ + t • y₁ + t ^ 2 • y₂ := by
  subst y₀
  subst y₁
  subst y₂
  rfl

end TauCeti

namespace LinearMap

/-- A linear map commutes with evaluation of a quadratic expression. -/
theorem map_quadraticPolynomial
    {A M N : Type*} [Semiring A] [AddCommMonoid M] [Module A M]
    [AddCommMonoid N] [Module A N] (f : M →ₗ[A] N) (t : A) (x₀ x₁ x₂ : M) :
    f (x₀ + t • x₁ + t ^ 2 • x₂) =
      f x₀ + t • f x₁ + t ^ 2 • f x₂ := by
  rw [map_add, map_add, map_smul, map_smul]

end LinearMap


