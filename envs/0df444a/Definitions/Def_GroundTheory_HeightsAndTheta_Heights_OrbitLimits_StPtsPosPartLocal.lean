-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StPtsPosPartLocal
-- name    : GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StPtsPosPartLocal
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T01:01:17.463426+00:00
-- url     : https://prove2.me/theorems/3fda139d-aa27-4e1f-8939-a867cce0f923
-- title:
--   St Pts Pos Part Local
-- statement:
--   Definitions and structural lemmas for St Pts Pos Part Local, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/StPtsPosPartLocal.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StPtsSheetSimpleNull
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StPtsPosPartProjIndep
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
open MeasureTheory
open ReciprocityTheory.ChartRestriction.G.Geo (MRing HermLine IsSmoothHerm IsArithVar IsGoodProj mcPts segre pot PBlk oneLine
  isSmoothHerm_oneLine)
def PtsPosPartLocal.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (e : ℕ)
    (Ψ Ψ' : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) (L : Fin e → HermLine ι)
    (g : ((Σ k, ι k) → ℂ) → ℝ) (z : (Σ k, ι k) → ℂ),
    IsArithVar P (e + 1) → IsGoodProj P Ψ → IsGoodProj P Ψ' → (∀ j, IsSmoothHerm (L j)) →
    Measurable g → (∀ (c : K → ℂ) (z' : (Σ k, ι k) → ℂ), (∀ k, c k ≠ 0) → g (fun p => c p.1 * z' p) = g z') →
    z ∈ mcPts P → IsSimpleSheetPt P Ψ ((Ψ (segre z) 0)⁻¹ • segre z) →
    IsSimpleSheetPt P Ψ' ((Ψ' (segre z) 0)⁻¹ • segre z) →
      ∃ W : Set ((Σ k, ι k) → ℂ), IsOpen W ∧ z ∈ W ∧
        (∀ (c : K → ℂ) (z' : (Σ k, ι k) → ℂ), (∀ k, c k ≠ 0) → ((fun p => c p.1 * z' p) ∈ W ↔ z' ∈ W)) ∧
        ∀ E : Set ((Σ k, ι k) → ℂ), MeasurableSet E →
          (∀ (c : K → ℂ) (z' : (Σ k, ι k) → ℂ), (∀ k, c k ≠ 0) → ((fun p => c p.1 * z' p) ∈ E ↔ z' ∈ E)) →
          E ⊆ W →
            ∫⁻ y, ENNReal.ofReal (ptsPosDens P Ψ (pot L) (E.indicator g) y) =
              ∫⁻ y, ENNReal.ofReal (ptsPosDens P Ψ' (pot L) (E.indicator g) y)
end GroundTheory.Heights₂.Heights


