-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_CoefETensGrpMul
-- name    : ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_CoefETensGrpMul
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T01:42:56.802425+00:00
-- url     : https://prove2.me/theorems/c19ca548-b61a-4c39-a40a-d48dc108953a
-- title:
--   Coef ETens Grp Mul
-- statement:
--   Definitions and structural lemmas for Coef ETens Grp Mul, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TensorRepresentations/CoefETensGrpMul.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_CoefDTensActPow
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open scoped Matrix
namespace ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ}
section Rep
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {ε : Fin n → Bool}
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {D : Submodule ℂ H}
  {E : Fin n → Fin n → Module.End ℂ D}
def coefLam (dual : Bool) (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (g : Matrix (Fin n) (Fin n) ℂ)
    (f : Fin n → H) : (Fin n → H) →L[ℂ] ℂ :=
  ∑ c, (innerSL ℂ (f c)).comp (∑ d, coefAm dual g c d • (σ g).comp (ContinuousLinearMap.proj d))
def CoefGood (E : Fin n → Fin n → Module.End ℂ D) (V : Submodule ℂ D) (X : Matrix (Fin n) (Fin n) ℂ)
    (r₀ : ℝ) : Prop :=
  ∀ v ∈ genSub E V, ∃ a : ℕ → ℝ, (∀ m, ‖((((actM E X) ^ m) v : D) : H)‖ ≤ a m) ∧
    ∀ s : ℝ, |s| < r₀ → Summable fun m : ℕ => a m * |s| ^ m / (m.factorial : ℝ)
end Rep
section Propag
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {ε : Fin n → Bool}
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {D : Submodule ℂ H}
  {E : Fin n → Fin n → Module.End ℂ D}
def CoefQ (dual : Bool) (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (E : Fin n → Fin n → Module.End ℂ D)
    (V' : Submodule ℂ D) (ι : D →ₗ[ℂ] (Fin n → D)) (f : Fin n → D) (z : D)
    (h : Matrix (Fin n) (Fin n) ℂ) : Prop :=
  ∀ y ∈ genSub E V', ∑ c, inner ℂ ((f c : D) : H) (coefTG dual σ h (fun d => ((ι y d : D) : H)) c) =
    inner ℂ ((z : D) : H) (σ h ((y : D) : H))
end Propag
end ReciprocityTheory.ChartRestriction.DS


