-- Prove2me | Definitions.Def_MomentComparison_Basic
-- name    : MomentComparison_Basic
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-24T10:10:45.0608+00:00
-- url     : https://prove2.me/theorems/ed8891d5-68be-4d24-a4cb-02bafbb60432
-- title:
--   Basic
-- statement:
--   Definitions and structural lemmas for Basic, from XinyuanXie-hub (XinyuanXie-hub/MomentComparison; see pinned Apache-2.0 LICENSE)'s pinned Sharp two-sided bounds on the moment comparison constant Cstar development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/XinyuanXie-hub/MomentComparison/blob/30aae604e14c2e7a22e5eb3bcd3cfd6d02f61772/MomentComparison/Basic.lean

module
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
set_option autoImplicit true
@[expose] public section
public section
@[expose] section
open scoped BigOperators
namespace MomentComparison
abbrev Cube (n : ℕ) := Fin n → Bool
noncomputable def cubeAverage {n : ℕ} (f : Cube n → ℝ) : ℝ :=
  (∑ x, f x) / (2 : ℝ) ^ n
def HasDegreeLE {n : ℕ} (f : Cube n → ℝ) (d : ℕ) : Prop :=
  ∀ s : Finset (Fin n), d < s.card →
    cubeAverage (fun x => f x * ∏ i ∈ s, if x i then 1 else -1) = 0
noncomputable def Cstar : ℝ :=
  sInf {C : ℝ | 0 < C ∧
    ∀ (n d : ℕ), 0 < n → 0 < d → ∀ f : Cube n → ℝ, HasDegreeLE f d →
      Real.sqrt (cubeAverage fun x => f x ^ 2) ≤ C ^ d * cubeAverage (fun x => |f x|)}
noncomputable def upperBase : ℝ :=
  sInf ((fun p : ℝ =>
    let r := Real.sqrt (p - 1)
    let θ := 2 * Real.arcsin (2 * r / p)
    let α : ℂ := (Real.pi / (2 * Real.pi - θ) : ℝ)
    let z := Complex.I * (r : ℂ)
    let a := (z - 1) ^ α
    let b := (z + 1) ^ α
    ‖(a + b) / (a - b)‖ ^ (p / (2 * (p - 2)))) '' Set.Ioi 2)
end MomentComparison


