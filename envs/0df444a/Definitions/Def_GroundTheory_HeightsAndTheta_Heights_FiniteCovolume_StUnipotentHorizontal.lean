-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StUnipotentHorizontal
-- name    : GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StUnipotentHorizontal
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-25T04:19:03.036127+00:00
-- url     : https://prove2.me/theorems/2388f318-a86f-5152-9ed8-6213b22f016c
-- title:
--   St Unipotent Horizontal
-- statement:
--   Definitions and structural lemmas for St Unipotent Horizontal, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/StUnipotentHorizontal.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StUnipotentCoordProper
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace GroundTheory.Heights₂.Heights.FiniteCovolume
open NumberField GroundTheory.Automorphic Module Matrix Topology
noncomputable section
variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [IsTotallyComplex E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]
def UnipotentHorizontal.Statement (h : HermitianForm F E W) (v : Basis ι E W) : Prop :=
  ∀ (D : ℕ) (La : AddSubgroup W) (x₀ w₀ : W), IsDIntegral h D La → x₀ ∈ La →
    IsHyperbolicPair h x₀ w₀ →
    ∃ K : Set (InfinitePlace E → ι → ℂ), IsCompact K ∧ ∀ n : unipRadical h v x₀,
      ∃ δ : unipRadical h v x₀, (δ : archUnitary h v) ∈ vecStabGroup h v La x₀ ∧
        ∃ t : InfinitePlace E → ℂ,
          unipCoord h v x₀ w₀ (δ * n) - (fun w => t w • vecAt v x₀ w) ∈ K
section Inhabitants
open GaussianPlane
end Inhabitants
end
end GroundTheory.Heights₂.Heights.FiniteCovolume


