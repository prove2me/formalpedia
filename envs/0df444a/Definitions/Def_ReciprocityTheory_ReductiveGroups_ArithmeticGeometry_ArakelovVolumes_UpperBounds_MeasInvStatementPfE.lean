-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_MeasInvStatementPfE
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_MeasInvStatementPfE
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T13:03:13.726403+00:00
-- url     : https://prove2.me/theorems/47e02cef-94a2-442c-8dc0-94a2e98fd502
-- title:
--   Meas Inv Statement Pf E
-- statement:
--   Definitions and structural lemmas for Meas Inv Statement Pf E, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/UpperBounds/MeasInvStatementPfE.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_MeasInvStatementPfD
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.MI
open Matrix MeasureTheory
noncomputable section
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {r : ℕ}
def dI (τ : ι) (b : Fin r) : UpI ι r := ⟨(τ, b, b), lt_irrefl b⟩
def jacU (y : UpI ι r → ℂ) : ℂ := ∏ i : Ix ι r, if i.2.2 < i.2.1 then y (dI i.1 i.2.2) else 1
def jacβ (β : ι → Matrix (Fin r) (Fin r) ℂ) : ℂ := ∏ i : Ix ι r, if i.2.2 < i.2.1 then β i.1 i.2.2 i.2.2 else 1
def Cy (ι : Type*) [Fintype ι] (r : ℕ) : Set (UpI ι r → ℂ) :=
  {y | ∀ i : UpI ι r, (i.1.2.1 = i.1.2.2 → 1 ≤ ‖y i‖ ∧ ‖y i‖ ≤ 2) ∧ (i.1.2.1 ≠ i.1.2.2 → ‖y i‖ ≤ 1)}
def K0 (ι : Type*) [Fintype ι] [DecidableEq ι] (r : ℕ) : ENNReal :=
  ∫⁻ y in Cy ι r, ENNReal.ofReal (Complex.normSq (jacU y))
end
end ReciprocityTheory.ChartRestriction.G.AR.Up.MI


