-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_ImportsTerSide
-- name    : GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_ImportsTerSide
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:23:52.120567+00:00
-- url     : https://prove2.me/theorems/a619b942-156c-4cd6-9ca1-e7651e8d5a94
-- title:
--   Imports Ter Side
-- statement:
--   Definitions and structural lemmas for Imports Ter Side, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/ImportsTerSide.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_InstFintypeSumElim
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_ScaledRankOneLeStandardRankOne
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_NumbersDVR_Bundles_pt_model_b42d523b4374

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.NumbersDVR
open IndefiniteRowSideFullHecke.NumbersDVR.Bundles (IsModelOver mcIdeal joinCoord fnField ptCoord noCoord pt_model join_model
  ptFlagModel)
def JoinTwoModels.Statement : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Ω : Type) [Field Ω]
    [Algebra O Ω] (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (x : (Σ k, ι k) → Ω) (d : ℕ), IsModelOver O (mcIdeal O x) d →
    ∀ (K₁ : Type) [Fintype K₁] (ι₁ : K₁ → Type) [∀ k, Fintype (ι₁ k)] (z₁ : (Σ k, ι₁ k) → Ω)
      (K₂ : Type) [Fintype K₂] (ι₂ : K₂ → Type) [∀ k, Fintype (ι₂ k)] (z₂ : (Σ k, ι₂ k) → Ω),
      IsModelOver O (mcIdeal O (joinCoord x z₁)) d → fnField O (joinCoord x z₁) = fnField O x →
      IsModelOver O (mcIdeal O (joinCoord x z₂)) d → fnField O (joinCoord x z₂) = fnField O x →
      IsModelOver O (mcIdeal O (joinCoord x (joinCoord z₁ z₂))) d ∧
        fnField O (joinCoord x (joinCoord z₁ z₂)) = fnField O x
end GroundTheory.Heights₂.Heights.NumbersDVR


