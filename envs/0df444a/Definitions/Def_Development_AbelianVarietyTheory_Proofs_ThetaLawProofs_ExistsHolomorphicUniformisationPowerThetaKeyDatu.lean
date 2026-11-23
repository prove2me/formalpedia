-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_ExistsHolomorphicUniformisationPowerThetaKeyDatu
-- name    : Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_ExistsHolomorphicUniformisationPowerThetaKeyDatu
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T12:24:55.270259+00:00
-- url     : https://prove2.me/theorems/d1d336c6-a18d-4080-9443-e5b1a7d882d1
-- title:
--   Exists Holomorphic Uniformisation Power Theta Key Datu
-- statement:
--   Definitions and structural lemmas for Exists Holomorphic Uniformisation Power Theta Key Datu, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/ExistsHolomorphicUniformisationPowerThetaKeyDatu.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_KeyFormula_KeyRuleOneOfKeyFormula
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TopLePreimageOfValAtNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_HolFamilyOfIsPullback
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_MapsAtLeA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_OneEqSpTranslZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
namespace GlobalTheory.PowUnif
def IsHolFamily {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {Z : Scheme.{0}} (c : E → (Sp ℂ ⟶ Z)) : Prop :=
  ∀ (U : Z.Opens) (f : Γ(Z, U)), IsOpen {z | ⊤ ≤ c z ⁻¹ᵁ U} ∧
    DifferentiableOn ℂ (fun z => valAt' (c z) U f) {z | ⊤ ≤ c z ⁻¹ᵁ U}
section Hol
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
end Hol
section Val
variable {X Y : Scheme.{0}}
end Val
section Blocks
variable {j g n : ℕ} (e : Fin j × Fin g ≃ Fin n)
def blockPr (i : Fin j) : (Fin n → ℂ) →L[ℂ] (Fin g → ℂ) :=
  ContinuousLinearMap.pi fun k => ContinuousLinearMap.proj (e (i, k))
def blockIn (i : Fin j) : (Fin g → ℂ) →L[ℂ] (Fin n → ℂ) :=
  ContinuousLinearMap.pi fun q => if i = (e.symm q).1 then ContinuousLinearMap.proj (e.symm q).2 else 0
def blockLat (Λ : Submodule ℤ (Fin g → ℂ)) : Submodule ℤ (Fin n → ℂ) where
  carrier := {z | ∀ i, blockPr e i z ∈ Λ}
  add_mem' := fun ha hb i => by rw [map_add]; exact Λ.add_mem (ha i) (hb i)
  zero_mem' := fun i => by rw [map_zero]; exact Λ.zero_mem
  smul_mem' := fun c z hz i => by rw [map_zsmul]; exact Λ.smul_mem c (hz i)
end Blocks
section Pow
variable {G' G : Over (Sp ℂ)} [GrpObj G'] [GrpObj G] {j : ℕ} (p : Out.IsPowGrp G' G j)
def powLift {T : Over (Sp ℂ)} (a : Fin j → (T ⟶ G)) : T ⟶ G' := p.lim.lift (Fan.mk _ a)
variable {L : LB G.left} {g : ℕ} (u : HolUnif G L g)
variable {L' : LB G'.left} {n : ℕ} (u' : HolUnif G' L' n)
end Pow
end GlobalTheory.PowUnif
end


