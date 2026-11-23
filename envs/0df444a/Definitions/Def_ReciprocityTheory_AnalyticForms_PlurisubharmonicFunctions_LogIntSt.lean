-- Prove2me | Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_LogIntSt
-- name    : ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_LogIntSt
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T15:14:52.474406+00:00
-- url     : https://prove2.me/theorems/04e45fca-f9ea-4df0-8a94-09f689aa9ec6
-- title:
--   Log Int St
-- statement:
--   Definitions and structural lemmas for Log Int St, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/LogIntSt.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.AnForm.A
open MeasureTheory
noncomputable section
def logMono {D : ℕ} (m : Fin D → ℤ) (z : Fin D → ℂ) : ℝ :=
  ∑ i, (m i : ℝ) * Real.log ‖z i‖
def LogNormLocIntCStatement : Prop :=
  LocallyIntegrable (fun z : ℂ => Real.log ‖z‖) volume
def LogCoordLocIntStatement : Prop :=
  ∀ (D : ℕ) (i : Fin D), LocallyIntegrable (fun z : Fin D → ℂ => Real.log ‖z i‖) volume
def LogMonoLocIntStatement : Prop :=
  ∀ (D : ℕ) (m : Fin D → ℤ), LocallyIntegrable (logMono m) volume
def LogMonoTestIntStatement : Prop :=
  ∀ (D : ℕ) (m : Fin D → ℤ) (f : (Fin D → ℂ) → ℝ), Continuous f → HasCompactSupport f →
    Integrable (fun z => f z * logMono m z) volume
def LogUnitMonoLocIntStatement : Prop :=
  ∀ (D : ℕ) (m : Fin D → ℤ) (U : Set (Fin D → ℂ)) (u : (Fin D → ℂ) → ℂ), IsOpen U →
    DifferentiableOn ℂ u U → (∀ z ∈ U, u z ≠ 0) →
    LocallyIntegrableOn (fun z => Real.log ‖u z * ∏ i, z i ^ m i‖) U volume
end
end ReciprocityTheory.AnForm.A


