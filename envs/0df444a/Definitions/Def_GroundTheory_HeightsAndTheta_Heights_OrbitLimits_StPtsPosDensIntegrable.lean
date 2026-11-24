-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StPtsPosDensIntegrable
-- name    : GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StPtsPosDensIntegrable
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:50:50.242631+00:00
-- url     : https://prove2.me/theorems/163d1d12-ca6e-4932-a00e-47096b152bec
-- title:
--   St Pts Pos Dens Integrable
-- statement:
--   Definitions and structural lemmas for St Pts Pos Dens Integrable, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/StPtsPosDensIntegrable.lean

import Mathlib
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
open ReciprocityTheory.ChartRestriction.G.Geo (MRing HermLine IsSmoothHerm IsArithVar IsGoodProj pot PBlk oneLine isSmoothHerm_oneLine)
def PtsPosDensIntegrable.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (e : ℕ)
    (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) (L : Fin e → HermLine ι)
    (g : ((Σ k, ι k) → ℂ) → ℝ),
    IsArithVar P (e + 1) → IsGoodProj P Ψ → (∀ j, IsSmoothHerm (L j)) → IsDegZeroSmooth g →
      Integrable (ptsPosDens P Ψ (pot L) g)
end GroundTheory.Heights₂.Heights


