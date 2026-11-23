-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_VolumeFundamentalDomainPeriodLattice
-- name    : Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_VolumeFundamentalDomainPeriodLattice
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T11:35:47.094973+00:00
-- url     : https://prove2.me/theorems/8ad56550-d710-4fe6-b77a-96d1b3600855
-- title:
--   Volume Fundamental Domain Period Lattice
-- statement:
--   Definitions and structural lemmas for Volume Fundamental Domain Period Lattice, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/VolumeFundamentalDomainPeriodLattice.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
namespace GlobalTheory.PeriodVol
def reImCoord (g : ℕ) : (Fin g → ℂ) ≃ₗ[ℝ] (Fin g ⊕ Fin g → ℝ) where
  toFun z := Sum.elim (fun i => (z i).re) (fun i => (z i).im)
  invFun p := fun i => ⟨p (Sum.inl i), p (Sum.inr i)⟩
  map_add' z w := by ext (i | i) <;> simp
  map_smul' c z := by ext (i | i) <;> simp
  left_inv z := rfl
  right_inv p := by ext (i | i) <;> rfl
def periodMap {g : ℕ} (τ : Matrix (Fin g) (Fin g) ℂ) : (Fin g → ℂ) →ₗ[ℝ] (Fin g → ℂ) :=
  ((reImCoord g).symm : (Fin g ⊕ Fin g → ℝ) →ₗ[ℝ] (Fin g → ℂ)) ∘ₗ
    Matrix.toLin' (Matrix.fromBlocks 1 (τ.map Complex.re) 0 (τ.map Complex.im)) ∘ₗ
      ((reImCoord g).symm.symm : (Fin g → ℂ) →ₗ[ℝ] (Fin g ⊕ Fin g → ℝ))
end GlobalTheory.PeriodVol
namespace GlobalTheory
open PeriodVol
end GlobalTheory


