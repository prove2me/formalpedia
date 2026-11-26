-- Prove2me | Definitions.Def_ClassicalComplexWPT_Basic
-- name    : ClassicalComplexWPT_Basic
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T17:55:44.201384+00:00
-- url     : https://prove2.me/theorems/8c30062d-05cf-5b4e-96a7-735e587867f4
-- title:
--   Basic
-- statement:
--   Definitions and structural lemmas for Basic, from BochaoKong (BochaoKong/classical-complex-wpt; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Classical complex-analytic Weierstrass preparation theorem development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/BochaoKong/classical-complex-wpt/blob/b4a7273fe5c9752753c52e10494097569089642d/ClassicalComplexWPT/Basic.lean

import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Complex.Basic
set_option autoImplicit true
open scoped BigOperators Topology
namespace ClassicalComplexWPT
abbrev Base (n : ℕ) := Fin n → ℂ
abbrev Ambient (n : ℕ) := Base n × ℂ
def lastSlice {n : ℕ} (f : Ambient n → ℂ) : ℂ → ℂ :=
  fun w ↦ f (0, w)
def ExactOrderInLastVariable {n : ℕ} (f : Ambient n → ℂ) (d : ℕ) : Prop :=
  (∀ k < d, iteratedDeriv k (lastSlice f) 0 = 0) ∧
    iteratedDeriv d (lastSlice f) 0 ≠ 0
def preparedPolynomial {n : ℕ} (d : ℕ) (a : Fin d → Base n → ℂ)
    (x : Ambient n) : ℂ :=
  x.2 ^ d + ∑ i : Fin d, a i x.1 * x.2 ^ (i : ℕ)
def IsWeierstrassPreparation {n : ℕ} (f : Ambient n → ℂ) (d : ℕ)
    (a : Fin d → Base n → ℂ) (u : Ambient n → ℂ) : Prop :=
  (∀ i, AnalyticAt ℂ (a i) 0) ∧
    (∀ i, a i 0 = 0) ∧
    AnalyticAt ℂ u 0 ∧
    u 0 ≠ 0 ∧
    f =ᶠ[𝓝 0] fun x ↦ u x * preparedPolynomial d a x
end ClassicalComplexWPT


