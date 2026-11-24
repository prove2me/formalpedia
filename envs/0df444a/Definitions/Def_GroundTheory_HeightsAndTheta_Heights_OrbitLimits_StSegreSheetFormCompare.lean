-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StSegreSheetFormCompare
-- name    : GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StSegreSheetFormCompare
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T05:06:08.232804+00:00
-- url     : https://prove2.me/theorems/51f9e17e-9daf-4426-a342-a213bd9e771a
-- title:
--   St Segre Sheet Form Compare
-- statement:
--   Definitions and structural lemmas for St Segre Sheet Form Compare, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/StSegreSheetFormCompare.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_SegreChartProjObjects
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_isSmoothHerm_oneLine

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
namespace GroundTheory.Heights₂.Heights
open ReciprocityTheory.ChartRestriction.G.Geo (HermLine IsSmoothHerm pot segre oneLine isSmoothHerm_oneLine)
def SegreSheetFormCompare.Statement : Prop :=
  ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (e : ℕ) (L : Fin e → HermLine ι),
    (∀ j, IsSmoothHerm (L j)) →
      ∃ C : ℝ, ∀ (z : (Fin e → ℂ) → (Σ k, ι k) → ℂ) (U : Set (Fin e → ℂ)) (y : Fin e → ℂ),
        IsOpen U → y ∈ U → DifferentiableOn ℂ z U → (∀ k, ∃ j, z y ⟨k, j⟩ ≠ 0) →
          |ReciprocityTheory.AnForm.maDens (fun j => pot L j ∘ z) y| ≤
            C * ReciprocityTheory.AnForm.maDens
              (fun _ => (fun w => Real.log (Real.sqrt (∑ i', ‖segre w i'‖ ^ 2))) ∘ z) y
end GroundTheory.Heights₂.Heights


