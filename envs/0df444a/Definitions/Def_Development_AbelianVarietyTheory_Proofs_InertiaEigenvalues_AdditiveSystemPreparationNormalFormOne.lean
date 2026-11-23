-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_AdditiveSystemPreparationNormalFormOne
-- name    : Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_AdditiveSystemPreparationNormalFormOne
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T17:32:28.283918+00:00
-- url     : https://prove2.me/theorems/48b9ad58-cbdf-4dd8-ae8c-da187ae59bb6
-- title:
--   Additive System Preparation Normal Form One
-- statement:
--   Definitions and structural lemmas for Additive System Preparation Normal Form One, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/AdditiveSystemPreparationNormalFormOne.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_MooreNorm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.PMonE
open Finset
section Prep
variable {F : Type} [NormedField F] {m : Type} [Fintype m]
def PrepBd (c : ℝ) (X : Matrix m m F) : Prop := ∀ i j, ‖X i j‖ ≤ c
noncomputable def prepV (q : ℕ) (M : ℕ → Matrix m m F) (A : Matrix m m F) (k : ℕ) : ℕ → Matrix m m F :=
  Nat.rec (motive := fun _ => ℕ → Matrix m m F) (fun _ => 0)
    (fun _ V n => M (n + 1) + V (n + 1) * A.map (fun a => a ^ q ^ (n + 1))) k
variable [IsUltrametricDist F]
end Prep
end GlobalTheory.PMonE
end


