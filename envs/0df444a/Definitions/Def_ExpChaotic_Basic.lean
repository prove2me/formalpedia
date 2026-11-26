-- Prove2me | Definitions.Def_ExpChaotic_Basic
-- name    : ExpChaotic_Basic
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T03:57:52.497282+00:00
-- url     : https://prove2.me/theorems/dfe754c6-8d87-450a-9c30-29f4e117627a
-- title:
--   Basic
-- statement:
--   Definitions and structural lemmas for Basic, from Lasse Rempe (LR-UK/exp-chaotic; initial proof architecture adapted under HOL Light BSD-style licence from John Harrison Examples/misiurewicz.ml per THIRD_PARTY_NOTICES.md; original Lean code Apache-2.0)'s pinned The complex exponential map is chaotic and Misiurewicz's theorem (Julia set equals C) development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LR-UK/exp-chaotic/blob/303b2d3d1121ebc3a86399de8f1e71c17a8b6dd8/ExpChaotic/Basic.lean

import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.Choose
import Mathlib.Tactic.Continuity
import Mathlib.Tactic.Convert
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
set_option autoImplicit true
open Function Filter Set Metric
open scoped Topology NNReal Uniformity
namespace ExponentialJuliaSetMisiurewicz
noncomputable section
abbrev exponentialMap : ℂ → ℂ := Complex.exp
abbrev expIterate (n : ℕ) : ℂ → ℂ := exponentialMap^[n]
def centralStrip : Set ℂ := {z | |z.im| ≤ Real.pi / 3}
def rightHalfPlane : Set ℂ := {z | 4 < z.re}
def wideStrip : Set ℂ := {z | |z.im| ≤ 2 * Real.pi}
def OnRealAxis (z : ℂ) : Prop := z.im = 0
def EventuallyMeetsRealAxis (V : Set ℂ) : Prop :=
  ∃ n : ℕ, ∃ z ∈ V, OnRealAxis (expIterate n z)
end
end ExponentialJuliaSetMisiurewicz


