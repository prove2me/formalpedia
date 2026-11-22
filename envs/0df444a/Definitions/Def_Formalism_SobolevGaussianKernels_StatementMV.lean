-- Prove2me | Definitions.Def_Formalism_SobolevGaussianKernels_StatementMV
-- name    : Formalism_SobolevGaussianKernels_StatementMV
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T19:12:52.981316+00:00
-- url     : https://prove2.me/theorems/13c3bac5-e432-4036-affb-96eee7bd98d9
-- title:
--   Statement MV
-- statement:
--   Definitions and structural lemmas for Statement MV, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SobolevGaussianKernels/StatementMV.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace Formalism.SL.MV
open Finset
noncomputable def kern {ι Mv : Type} [Fintype Mv] [DecidableEq ι] (src tgt : Mv → ι) (μ : Mv → ℝ) (i j : ι) : ℝ :=
  ∑ m ∈ univ.filter (fun m => src m = i ∧ tgt m = j), μ m
def MoveKernel : Prop :=
  ∀ (ι Mv : Type) [Fintype ι] [Fintype Mv] [DecidableEq ι] (src tgt : Mv → ι) (μ : Mv → ℝ) (inv : Mv → Mv),
    (∀ m, inv (inv m) = m) → (∀ m, src (inv m) = tgt m) → (∀ m, tgt (inv m) = src m) → (∀ m, μ (inv m) = μ m) →
    ∀ i j, kern src tgt μ i j = kern src tgt μ j i
def MoveBound : Prop :=
  ∀ (ι Mv : Type) [Fintype ι] [Fintype Mv] [DecidableEq ι] (src tgt : Mv → ι) (μ : Mv → ℝ) (inv : Mv → Mv)
    (w : ι → ℂ) (χ : Mv → ℂ) (ε₁ ε₂ : ℝ),
    (∀ m, inv (inv m) = m) → (∀ m, src (inv m) = tgt m) → (∀ m, tgt (inv m) = src m) → (∀ m, μ (inv m) = μ m) →
    (∀ m, w (tgt m) = w (src m) * χ m) →
    (∀ i, ‖w i‖ ≤ 1) →
    (∀ i, |(∑ m ∈ univ.filter (fun m => src m = i), μ m) - 1| ≤ ε₁) →
    (∀ i, ‖∑ m ∈ univ.filter (fun m => src m = i), (μ m : ℂ) * χ m‖ ≤ ε₂) →
    ‖∑ i, w i‖ ≤ (ε₁ + ε₂) * (Fintype.card ι : ℝ)
end Formalism.SL.MV


