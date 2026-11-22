-- Prove2me | Definitions.Def_LeanPool_ZhangYeungInequality_Theorem2
-- name    : LeanPool_ZhangYeungInequality_Theorem2
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T14:53:17.129683+00:00
-- url     : https://prove2.me/theorems/51fdc53c-5074-45b1-84e6-88e2f710e68a
-- title:
--   Theorem2
-- statement:
--   Definitions and structural lemmas for Theorem2, from Christopher Boone; LeanPool contributors's pinned The Zhang-Yeung non-Shannon information inequality development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/Theorem2.lean

module
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_ForMathlib_Entropy_Basic
public import Definitions.Def_LeanPool_ZhangYeungInequality_Delta
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_Analysis_SpecialFunctions_NegMulLog
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_Data_Set_Basic
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_MeasureTheory_Measure_Real
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace ZhangYeung
open MeasureTheory ProbabilityTheory Real
open scoped ZhangYeungPFR
variable {Ω : Type*} [MeasurableSpace Ω]
  {S₁ S₂ S₃ S₄ : Type*}
  [Fintype S₁] [Fintype S₂] [Fintype S₃] [Fintype S₄]
  [MeasurableSpace S₁] [MeasurableSpace S₂]
  [MeasurableSpace S₃] [MeasurableSpace S₄]
  [MeasurableSingletonClass S₁] [MeasurableSingletonClass S₂]
  [MeasurableSingletonClass S₃] [MeasurableSingletonClass S₄]
noncomputable def ptilde
    (X : Ω → S₁) (Y : Ω → S₂) (Z : Ω → S₃) (U : Ω → S₄) (μ : Measure Ω) :
    S₁ × S₂ × S₃ × S₄ → ℝ := fun ⟨x, y, z, u⟩ =>
  (μ.map (fun ω => (X ω, Z ω, U ω))).real {(x, z, u)}
    * (μ.map (fun ω => (Y ω, Z ω, U ω))).real {(y, z, u)}
    / (μ.map (fun ω => (Z ω, U ω))).real {(z, u)}
noncomputable def phat
    (X : Ω → S₁) (Y : Ω → S₂) (Z : Ω → S₃) (U : Ω → S₄) (μ : Measure Ω) :
    S₁ × S₂ × S₃ × S₄ → ℝ := fun ⟨x, y, z, u⟩ =>
  (μ.map (fun ω => (X ω, Z ω))).real {(x, z)}
    * (μ.map (fun ω => (X ω, U ω))).real {(x, u)}
    * (μ.map (fun ω => (Y ω, Z ω))).real {(y, z)}
    * (μ.map (fun ω => (Y ω, U ω))).real {(y, u)}
    / ((μ.map Z).real {z} * (μ.map U).real {u} * (μ.map X).real {x} * (μ.map Y).real {y})
noncomputable def pJoint
    (X : Ω → S₁) (Y : Ω → S₂) (Z : Ω → S₃) (U : Ω → S₄) (μ : Measure Ω) :
    S₁ × S₂ × S₃ × S₄ → ℝ := fun t =>
  (μ.map (fun ω => (X ω, Y ω, Z ω, U ω))).real {t}
end ZhangYeung


