-- Prove2me | Definitions.Def_Development_AutomorphicArithmetic_DedekindLFunctions_CharFamily
-- name    : Development_AutomorphicArithmetic_DedekindLFunctions_CharFamily
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:03:32.675936+00:00
-- url     : https://prove2.me/theorems/fd3fbaee-6054-441b-a83b-b3c50708dcbe
-- title:
--   Char Family
-- statement:
--   Definitions and structural lemmas for Char Family, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/DedekindLFunctions/CharFamily.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped ArithmeticFunction.vonMangoldt
open Complex
noncomputable section
namespace Deduction
def ramp (f : ℕ → ℂ) (y : ℝ) : ℂ :=
  ∑ n ∈ Finset.range (⌊y⌋₊ + 1), (Λ n : ℂ) * f n * ((max (y / n - 1) 0 : ℝ) : ℂ)
open Classical in

def Gchi {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (y : ℝ) : ℂ :=
  if χ = 1 then
    ramp (fun n => χ n) y - ((y * Real.log y : ℝ) : ℂ) + (((1 + Real.eulerMascheroniConstant) * y : ℝ) : ℂ)
  else
    ramp (fun n => χ n) y + (y : ℂ) * (deriv (DirichletCharacter.LFunction χ) 1 / DirichletCharacter.LFunction χ 1)
def G (y : ℝ) : ℝ :=
  (ramp (fun _ => 1) y).re - y * Real.log y + (1 + Real.eulerMascheroniConstant) * y
structure CharFamily where
  ι : Type
  [fin : Fintype ι]
  N : ι → ℕ
  [nz : ∀ i, NeZero (N i)]
  χ : ∀ i, DirichletCharacter ℂ (N i)
  a : ι → ℝ
  a_pos : ∀ i, 0 < a i
  adm : ∀ i, N i = 1 ∨ χ i ≠ 1
attribute [instance] CharFamily.fin CharFamily.nz
def Gm (F : CharFamily) (y : ℝ) : ℝ := ∑ i, F.a i * (Gchi (F.χ i) y).re
def ZeroFree (F : CharFamily) (θ : ℝ) : Prop :=
  ∀ i, ∀ s : ℂ, θ < s.re → DirichletCharacter.LFunction (F.χ i) s ≠ 0
def WindowHyp (F : CharFamily) (θ δ : ℝ) : Prop :=
  ∀ η : ℝ, 0 < η → ∀ Y₀ : ℝ, ∃ Y : ℝ, Y₀ ≤ Y ∧ ∃ R : ℝ → ℝ,
    MeasureTheory.IntegrableOn (fun y => R y * y ^ (-θ - 1)) (Set.Icc Y (Y ^ (1 + δ))) ∧
    (∀ y ∈ Set.Icc Y (Y ^ (1 + δ)), 0 ≤ R y ∧ Gm F y ≤ R y) ∧
    ∫ y in Set.Icc Y (Y ^ (1 + δ)), R y * y ^ (-θ - 1) ≤ Y ^ η
end Deduction
end


