-- Prove2me | Definitions.Def_ReciprocityTheory_GeometryOfNumbers_SphericalMonomials_MonoNormSq
-- name    : ReciprocityTheory_GeometryOfNumbers_SphericalMonomials_MonoNormSq
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:13:45.049036+00:00
-- url     : https://prove2.me/theorems/4c449a01-d768-48b5-a549-6980c9496ea8
-- title:
--   Mono Norm Sq
-- statement:
--   Definitions and structural lemmas for Mono Norm Sq, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GeometryOfNumbers/SphericalMonomials/MonoNormSq.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace ReciprocityTheory.GeometryOfNumbersTheory
open MeasureTheory
def sqN {N : ℕ} (z : Fin N → ℂ) : ℝ :=
  ∑ i, ‖z i‖ ^ 2
def gaussC (N : ℕ) : Measure (Fin N → ℂ) :=
  volume.withDensity fun z => ENNReal.ofReal ((Real.pi ^ N)⁻¹ * Real.exp (-sqN z))
def sphProb (N : ℕ) : Measure (Fin N → ℂ) :=
  (gaussC N).map fun z => (((Real.sqrt (sqN z))⁻¹ : ℝ) : ℂ) • z
def monoC {N : ℕ} (a : Fin N → ℕ) (z : Fin N → ℂ) : ℂ :=
  ∏ i, z i ^ a i
def monoNormSq {D : ℕ} (a : Fin (D + 1) → ℕ) : ℝ :=
  ((∏ i, (a i).factorial : ℕ) : ℝ) * (D.factorial : ℝ) / (((∑ i, a i) + D).factorial : ℝ)
def chiP (D n : ℕ) : ℝ :=
  -(1 / 2) * ∑ a ∈ Finset.Nat.antidiagonalTuple (D + 1) n, Real.log (monoNormSq a)
end ReciprocityTheory.GeometryOfNumbersTheory


