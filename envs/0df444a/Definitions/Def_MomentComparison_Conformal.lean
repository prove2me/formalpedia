-- Prove2me | Definitions.Def_MomentComparison_Conformal
-- name    : MomentComparison_Conformal
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-24T10:14:16.295105+00:00
-- url     : https://prove2.me/theorems/750620aa-718b-4764-96ad-1ca21d2d432b
-- title:
--   Conformal
-- statement:
--   Definitions and structural lemmas for Conformal, from XinyuanXie-hub (XinyuanXie-hub/MomentComparison; see pinned Apache-2.0 LICENSE)'s pinned Sharp two-sided bounds on the moment comparison constant Cstar development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/XinyuanXie-hub/MomentComparison/blob/30aae604e14c2e7a22e5eb3bcd3cfd6d02f61772/MomentComparison/Conformal.lean

module
public import Mathlib.Analysis.Complex.AbsMax
public import Mathlib.Analysis.Complex.RemovableSingularity
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Definitions.Def_MomentComparison_Lens
public import Definitions.Def_MomentComparison_ComplexPower
public import Definitions.Def_MomentComparison_LensAngle
public import Definitions.Def_MomentComparison_LensEvaluation
public import Mathlib.Algebra.Polynomial.Eval.Degree
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
set_option autoImplicit true
@[expose] public section
public section
@[expose] section
open scoped BigOperators
open Set Metric
namespace MomentComparison
@[expose] noncomputable def lensFactor (p : ℝ) : ℝ :=
  let r := Real.sqrt (p - 1)
  let θ := 2 * Real.arcsin (2 * r / p)
  let α : ℂ := (Real.pi / (2 * Real.pi - θ) : ℝ)
  let z := Complex.I * (r : ℂ)
  let a := (z - 1) ^ α
  let b := (z + 1) ^ α
  ‖(a + b) / (a - b)‖
noncomputable def diskPlus (β : ℝ) (t : ℂ) : ℂ := (1 + t) ^ (β : ℂ)
noncomputable def diskMinus (β : ℝ) (t : ℂ) : ℂ := (1 - t) ^ (β : ℂ)
noncomputable def diskNumerator (β : ℝ) (t : ℂ) : ℂ :=
  diskMinus β t + diskPlus β t
noncomputable def diskDenominator (β : ℝ) (t : ℂ) : ℂ :=
  diskMinus β t - diskPlus β t
noncomputable def normalizedInverse (β r : ℝ) (t : ℂ) : ℂ :=
  diskNumerator β t / dslope (diskDenominator β) 0 t / (Complex.I * (r : ℂ))
end MomentComparison


