-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsFinsetOfMemNhds
-- name    : Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsFinsetOfMemNhds
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T11:02:30.936258+00:00
-- url     : https://prove2.me/theorems/c326c7ce-325a-4163-841b-df1ab9e6cfc7
-- title:
--   Exists Finset Of Mem Nhds
-- statement:
--   Definitions and structural lemmas for Exists Finset Of Mem Nhds, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsFinsetOfMemNhds.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_DifferentiableOnLeftInverse
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_IsPreconnectedBlockUnits
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Matrix
open scoped ComplexConjugate
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
namespace GlobalTheory.PeriodCoord
noncomputable section
variable {g : ℕ}
theorem herm_add_left (M : Matrix (Fin g) (Fin g) ℂ) (z z' w : Fin g → ℂ) :
    hermForm M (z + z') w = hermForm M z w + hermForm M z' w := by
  simp [hermForm]
theorem herm_add_right (M : Matrix (Fin g) (Fin g) ℂ) (z w w' : Fin g → ℂ) :
    hermForm M z (w + w') = hermForm M z w + hermForm M z w' := by
  simp [hermForm, mulVec_add]
theorem herm_smul_left (M : Matrix (Fin g) (Fin g) ℂ) (c : ℂ) (z w : Fin g → ℂ) :
    hermForm M (c • z) w = c * hermForm M z w := by
  simp [hermForm]
theorem herm_smul_right (M : Matrix (Fin g) (Fin g) ℂ) (c : ℂ) (z w : Fin g → ℂ) :
    hermForm M z (c • w) = conj c * hermForm M z w := by
  simp [hermForm, mulVec_smul]
def imForm (M : Matrix (Fin g) (Fin g) ℂ) : (Fin g → ℂ) →ₗ[ℝ] (Fin g → ℂ) →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (fun z w => (hermForm M z w).im)
    (fun z z' w => by rw [herm_add_left, Complex.add_im])
    (fun c z w => by
      rw [show c • z = (c : ℂ) • z from rfl, herm_smul_left]; simp)
    (fun z w w' => by rw [herm_add_right, Complex.add_im])
    (fun c z w => by
      rw [show c • w = (c : ℂ) • w from rfl, herm_smul_right]; simp)
def realMap (A B : Matrix (Fin g) (Fin g) ℂ) : (Fin g → ℂ) →ₗ[ℝ] (Fin g → ℂ) where
  toFun z := A *ᵥ z + B *ᵥ star z
  map_add' z w := by simp only [star_add, mulVec_add]; abel
  map_smul' c z := by
    change A *ᵥ ((c : ℂ) • z) + B *ᵥ star ((c : ℂ) • z) = (c : ℂ) • _
    simp only [star_smul, mulVec_smul, smul_add, RCLike.star_def, Complex.conj_ofReal]
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {ty : Fin g → (E →+* ℂ)}
def colMat {L : Type} (α : Fin g → (L →₀ ℂ)) (f : L → Fin g → ℂ) : Matrix (Fin g) (Fin g) ℂ :=
  Matrix.of fun i j => ∑ x ∈ (α j).support, α j x * f x i
def actMat (ty : Fin g → (E →+* ℂ)) (a : 𝓞 E) : Matrix (Fin g) (Fin g) ℂ := diagonal fun i => ty i (a : E)
end
end GlobalTheory.PeriodCoord


