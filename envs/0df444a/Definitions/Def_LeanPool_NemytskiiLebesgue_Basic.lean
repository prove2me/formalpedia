-- Prove2me | Definitions.Def_LeanPool_NemytskiiLebesgue_Basic
-- name    : LeanPool_NemytskiiLebesgue_Basic
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T18:32:50.184444+00:00
-- url     : https://prove2.me/theorems/c14a9ac8-8bf1-4502-b8ea-73a4a06d1d7f
-- title:
--   Basic
-- statement:
--   Definitions and structural lemmas for Basic, from Petr Girg; Petr Nečesal; Martin Dvořák; Jakub Psutka; LeanPool contributors's pinned Nemytskii operators on Lebesgue spaces development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/NemytskiiLebesgue/Basic.lean

module
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
public import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
public import Mathlib.MeasureTheory.Function.StronglyMeasurable.Inner
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Tactic.Cases
public import Mathlib.Tactic.Have
set_option autoImplicit true
@[expose] public section
public section
@[expose] section
namespace NemytskiiLebesgue
open scoped NemytskiiLebesgue
open MeasureTheory
open scoped ENNReal
@[expose] noncomputable def integralLpNorm {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] (f : Ω → E) (p : ℝ≥0∞) (μ : Measure Ω) : ℝ≥0∞ :=
  if p = 0 then 0 else if p = ⊤ then eLpNormEssSup f μ else eLpNorm' f p.toReal μ
open scoped ENNReal
scoped prefix:max "↱" => ENNReal.ofReal
scoped notation:max "↓"t:arg => (fun _ => t)
scoped postfix:max ".→" => Iff.mp
scoped postfix:max ".←" => Iff.mpr
scoped notation:max "ℝ^"n:max => EuclideanSpace ℝ (Fin n)
open scoped RealInnerProductSpace
open MeasureTheory
@[expose] noncomputable def normSMulSelf {T : Type*} {n : ℕ} (_ : T) (ξ : ℝ^n) : ℝ^n := ‖ξ‖ • ξ
end NemytskiiLebesgue


