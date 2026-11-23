-- Prove2me | Definitions.Def_ReciprocityTheory_AnalyticForms_MaIntEmpty
-- name    : ReciprocityTheory_AnalyticForms_MaIntEmpty
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T12:39:53.44081+00:00
-- url     : https://prove2.me/theorems/bddd27f2-b41b-41b3-9207-a2f0d30b02f7
-- title:
--   Ma Int Empty
-- statement:
--   Definitions and structural lemmas for Ma Int Empty, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/MaIntEmpty.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.AnForm
open MeasureTheory
noncomputable section
section Levi
variable {ι : Type*} [Fintype ι]
def levi (φ : (ι → ℂ) → ℝ) (z w : ι → ℂ) : ℝ :=
  (fderiv ℝ (fderiv ℝ φ) z w w + fderiv ℝ (fderiv ℝ φ) z (Complex.I • w) (Complex.I • w)) / 4
end Levi
section MongeAmpere
variable {D : ℕ}
def hessC (φ : (Fin D → ℂ) → ℝ) (z : Fin D → ℂ) : Matrix (Fin D) (Fin D) ℂ :=
  fun i j =>
    let H := fderiv ℝ (fderiv ℝ φ) z
    let ei : Fin D → ℂ := Pi.single i 1
    let ej : Fin D → ℂ := Pi.single j 1
    ((H ei ej + H (Complex.I • ei) (Complex.I • ej) : ℝ) +
      Complex.I * ((H ei (Complex.I • ej) - H (Complex.I • ei) ej : ℝ))) / 4
def mdisc (A : Fin D → Matrix (Fin D) (Fin D) ℂ) : ℂ :=
  (1 / (D.factorial : ℂ)) *
    ∑ S : Finset (Fin D), (-1) ^ (D - S.card) * (∑ k ∈ S, A k).det
def maDens (φ : Fin D → (Fin D → ℂ) → ℝ) (z : Fin D → ℂ) : ℝ :=
  (D.factorial : ℝ) * (2 / Real.pi) ^ D * (mdisc fun k => hessC (φ k) z).re
def maInt (φ : Fin D → (Fin D → ℂ) → ℝ) (g : (Fin D → ℂ) → ℝ) (U : Set (Fin D → ℂ)) : ℝ :=
  ∫ z in U, g z * maDens φ z
end MongeAmpere
end
end ReciprocityTheory.AnForm


