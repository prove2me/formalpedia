-- Prove2me | Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_Window
-- name    : Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_Window
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T20:36:43.495225+00:00
-- url     : https://prove2.me/theorems/d3f19584-5abd-4fea-a5e6-a6391315a184
-- title:
--   Window
-- statement:
--   Definitions and structural lemmas for Window, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/Window.lean

import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_ExplicitFormulaErrorOfHostConditions
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace Formalism.HC
def HasWindows (S : Set ℝ) (la : ℝ) : Prop :=
  ∀ y : ℝ, ∃ Y : ℝ, y ≤ Y ∧ ∀ x : ℝ, Y ≤ x → x ≤ Y ^ la → x ∈ S
namespace Level
variable (Λ : Level)
def LandauWinAt (la : ℝ) : Prop :=
  ∀ θ : ℝ, 0 < θ → θ < 1 → (∃ ψ ∈ Λ.KEPT, ∃ s : ℂ, θ < s.re ∧ DirichletCharacter.LFunction ψ.χ s = 0) →
    ∃ Y0 : ℝ, ∀ Y ≥ Y0, ∃ y : ℝ, Y ≤ y ∧ y ≤ Y ^ la ∧ y ^ θ < Λ.Gm y
def LandauWin : Prop := ∀ la : ℝ, 1 < la → Λ.LandauWinAt la
def FormBAt (la : ℝ) : Prop :=
  ∀ θ : ℝ, 0 < θ → θ < 1 → HasWindows {x | Λ.Gm x ≤ x ^ θ} la → Λ.ZeroFreeAbove θ
def FormB : Prop := ∀ la : ℝ, 1 < la → Λ.FormBAt la
variable {Λ}
end Level
end Formalism.HC
end


