-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StUnipotentCoordProper
-- name    : GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StUnipotentCoordProper
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-25T03:41:00.650997+00:00
-- url     : https://prove2.me/theorems/c6ffb5f3-6820-429a-9866-bd8a3a3d1241
-- title:
--   St Unipotent Coord Proper
-- statement:
--   Definitions and structural lemmas for St Unipotent Coord Proper, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/StUnipotentCoordProper.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StatementsStabilizerLevi
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
section Coordinate
variable {F E : Type*} [Field F] [Field E] [Algebra F E] [Algebra.IsQuadraticExtension F E]
  [NumberField E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]
def unipCoord (h : HermitianForm F E W) (v : Basis ι E W) (x₀ w₀ : W) (n : unipRadical h v x₀) :
    InfinitePlace E → ι → ℂ :=
  fun w => (((n : archUnitary h v) : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ) *ᵥ vecAt v w₀ w -
    vecAt v w₀ w
def UnipotentCoordProper.Statement [NumberField F] [IsTotallyReal F] [IsTotallyComplex E]
    (h : HermitianForm F E W) (v : Basis ι E W) : Prop :=
  ∀ x₀ w₀ : W, IsHyperbolicPair h x₀ w₀ → ∀ K : Set (InfinitePlace E → ι → ℂ), IsCompact K →
    IsCompact {n : unipRadical h v x₀ | unipCoord h v x₀ w₀ n ∈ K}
end Coordinate
section Inhabitants
open GaussianPlane
end Inhabitants
end
end GroundTheory.Heights₂.Heights.FiniteCovolume


