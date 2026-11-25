-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermFramePairNormalFormCongruenceLiftSmallGroup
-- name    : Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermFramePairNormalFormCongruenceLiftSmallGroup
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-25T05:25:39.008622+00:00
-- url     : https://prove2.me/theorems/5d873cec-42c7-5bd6-a484-8b653c05da77
-- title:
--   Herm Frame Pair Normal Form Congruence Lift Small Group
-- statement:
--   Definitions and structural lemmas for Herm Frame Pair Normal Form Congruence Lift Small Group, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/HermFramePairNormalFormCongruenceLiftSmallGroup.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FlagPairDefinitePartLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NormalFormDualOrthogonalLast
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermFramePairNormalFormGeometrySummaryStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermFramePairCommonUnipotentStabiliserSummary
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsIntegerAddStarEqOneOfIsCMUnram
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical nonZeroDivisors
namespace GlobalTheory.DegCnt.LiftS
section Ideals
variable {K : Type} [Field K] [NumberField K] [StarRing K]
end Ideals
section Abstract
variable {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V]
def levi (p q s : V →ₗ[K] V) : V →ₗ[K] V := s ∘ₗ p + (1 - p - q) ∘ₗ s ∘ₗ (1 - p - q) + q ∘ₗ s ∘ₗ q
def trans (H : HermSpace K V) (h z : V) (T τ : K) : V →ₗ[K] V :=
  LinearMap.id - T⁻¹ • (H.B.flip z).smulRight h + T⁻¹ • (H.B.flip h).smulRight z
    + (τ * T⁻¹) • (H.B.flip h).smulRight h
end Abstract
section Flag
variable {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V] {H : HermSpace K V} {r : ℕ}
end Flag
section Conc
variable {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V]
  {H : HermSpace K V} {r : ℕ} (N : NF H r)
def pI : V →ₗ[K] V := ∑ b ∈ Finset.univ.filter (fun b : Fin r => N.j ≤ b.val),
  (H.B.flip (N.ist b)).smulRight (N.F.e b.castSucc)
def qI : V →ₗ[K] V := ∑ b ∈ Finset.univ.filter (fun b : Fin r => N.j ≤ b.val),
  (H.B.flip (N.F.e b.castSucc)).smulRight (N.ist b)
end Conc
section Lat
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] {H : HermSpace K V} {r : ℕ} (N : NF H r)
noncomputable def Pst : Submodule (𝓞 K) V := ⨆ a : Fin r, ⨆ _ : N.j ≤ a.val, line (ipow N.𝔡 ((r : ℤ) - a.val)) (N.ist a)
end Lat
section Main
variable {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V] {H : HermSpace K V} {r : ℕ}
end Main
end GlobalTheory.DegCnt.LiftS


