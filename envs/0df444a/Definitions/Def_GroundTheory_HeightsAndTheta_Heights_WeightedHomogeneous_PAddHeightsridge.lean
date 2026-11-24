-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_PAddHeightsridge
-- name    : GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_PAddHeightsridge
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:55:43.320809+00:00
-- url     : https://prove2.me/theorems/36a303c0-2fb6-4bfb-bd8b-e6183706def6
-- title:
--   PAdd Heightsridge
-- statement:
--   Definitions and structural lemmas for PAdd Heightsridge, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/PAddHeightsridge.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights
open MvPolynomial ReciprocityTheory.ChartRestriction.G
noncomputable section
namespace AddBlockBridge
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ} {Ω : Type} [Field Ω]
set_option linter.unusedSectionVars false
abbrev ConeField (ι Ω : Type) [Field Ω] : Type := FractionRing (MvPolynomial ι Ω)
def constMap (ι : Type) : Ω →+* ConeField ι Ω :=
  (algebraMap (MvPolynomial ι Ω) (ConeField ι Ω)).comp C
def varT (k : ι) : ConeField ι Ω := algebraMap (MvPolynomial ι Ω) (ConeField ι Ω) (X k)
def coneHom (y : Coord n → Ω) : MvPolynomial (Coord n) ℤ →+* ConeField ι Ω :=
  (algebraMap (MvPolynomial ι Ω) (ConeField ι Ω)).comp (Geo.mConeMap (ι := blockIdx n) y).toRingHom
theorem coneHom_apply (y : Coord n → Ω) (f : MvPolynomial (Coord n) ℤ) :
    coneHom y f = algebraMap (MvPolynomial ι Ω) (ConeField ι Ω) (Geo.mConeMap (ι := blockIdx n) y f) := rfl
theorem mem_mCoordIdeal_iff (y : Coord n → Ω) (f : MvPolynomial (Coord n) ℤ) :
    f ∈ Geo.mCoordIdeal (ι := blockIdx n) y ↔ coneHom y f = 0 := by
  rw [Geo.mCoordIdeal, RingHom.mem_ker, coneHom_apply,
    map_eq_zero_iff _ (IsFractionRing.injective (MvPolynomial ι Ω) (ConeField ι Ω))]
variable (P : ArithVariety n) (y : Coord n → Ω) (hP : P.ideal = Geo.mCoordIdeal (ι := blockIdx n) y)
def coordHom : P.CoordRing →+* ConeField ι Ω :=
  Ideal.Quotient.lift P.ideal (coneHom y) fun f hf ↦ by
    rw [hP] at hf
    exact (mem_mCoordIdeal_iff y f).mp hf
theorem coordHom_injective : Function.Injective (coordHom P y hP) :=
  RingHom.lift_injective_of_ker_le_ideal _ _ fun f hf ↦ by
    rw [hP]
    exact (mem_mCoordIdeal_iff y f).mpr (RingHom.mem_ker.mp hf)
def funHom : P.FunField →+* ConeField ι Ω := IsFractionRing.lift (coordHom_injective P y hP)
end AddBlockBridge
end
end GroundTheory.Heights₂.Heights


