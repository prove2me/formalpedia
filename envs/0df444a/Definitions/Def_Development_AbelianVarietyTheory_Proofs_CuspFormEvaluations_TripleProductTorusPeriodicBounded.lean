-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_TripleProductTorusPeriodicBounded
-- name    : Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_TripleProductTorusPeriodicBounded
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T15:34:11.974949+00:00
-- url     : https://prove2.me/theorems/78f5e1f1-a056-4498-9e25-882efee97baf
-- title:
--   Triple Product Torus Periodic Bounded
-- statement:
--   Definitions and structural lemmas for Triple Product Torus Periodic Bounded, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/TripleProductTorusPeriodicBounded.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwoChartAtlas_TwoChartSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_HermFormPullEqOfLbIsoPow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TopLePreimageOfValAtNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_HolFamilyOfIsPullback
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_AppellHumbertDataOfIsoCube
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Complex Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (rosatiφ rosatiε zero2)
open GlobalTheory.JetSer (IsNormRos primφ primε)
open GlobalTheory.CubeValues GlobalTheory.AppellHumbertTrivial
open scoped BigOperators Real
noncomputable section
namespace GlobalTheory.FrameUnits
section Analysis
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
end Analysis
variable {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} (u : HolUnif A L g)
def psumLin (g : ℕ) (I : ULift.{0} (Finset (Fin 3))) : (Fin 3 → Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ) :=
  ∑ a ∈ I.down, LinearMap.proj a
def pt2 (x : (Fin g → ℂ) × (Fin g → ℂ)) : Sp ℂ ⟶ (A ⊗ A).left := (lift (u.ex x.1) (u.ex x.2)).left
def rosatiLin (F G : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)) :
    Fin 6 → ((Fin g → ℂ) × (Fin g → ℂ)) →ₗ[ℂ] (Fin g → ℂ) :=
  ![F ∘ₗ LinearMap.fst ℂ _ _ + LinearMap.snd ℂ _ _, F ∘ₗ LinearMap.fst ℂ _ _, LinearMap.snd ℂ _ _,
    LinearMap.fst ℂ _ _ + G ∘ₗ LinearMap.snd ℂ _ _, LinearMap.fst ℂ _ _, G ∘ₗ LinearMap.snd ℂ _ _]
def primLin (W : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)) : Fin 5 → (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ) :=
  ![LinearMap.id, LinearMap.id + W, LinearMap.id, W, 0]
end GlobalTheory.FrameUnits


