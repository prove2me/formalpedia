-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_HeightCentredPlacesFinite
-- name    : GroundTheory_HeightsAndTheta_Heights_HeightComparison_HeightCentredPlacesFinite
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T01:34:59.69428+00:00
-- url     : https://prove2.me/theorems/bcc32189-8542-4c31-9b47-c31eb7d2b26f
-- title:
--   Height Centred Places Finite
-- statement:
--   Definitions and structural lemmas for Height Centred Places Finite, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightComparison/HeightCentredPlacesFinite.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_HeightOrbitChart
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ComplexAt_algebraMap_apply_de37bb391a59

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
open NumberField
def CentredPlacesFinite.Statement : Prop :=
  ∀ (L : Type) [Field L] [NumberField L] (O : Subalgebra ℤ L), Algebra.FiniteType ℤ O →
    IsFractionRing O L → ∀ (m : Ideal O) [m.IsMaximal],
      {w : FinitePlace L | AbsCentredAt O m fun t ↦ w t}.Finite
example : ∃ (O : Subalgebra ℤ ℚ) (m : Ideal O), Algebra.FiniteType ℤ O ∧
    IsFractionRing O ℚ ∧ m.IsMaximal := by
  let e : (⊥ : Subalgebra ℤ ℚ) ≃ₐ[ℤ] ℤ := Algebra.botEquivOfInjective Int.cast_injective
  have hft : Algebra.FiniteType ℤ (⊥ : Subalgebra ℤ ℚ) := Algebra.FiniteType.equiv inferInstance e.symm
  have hfr : IsFractionRing (⊥ : Subalgebra ℤ ℚ) ℚ := by
    refine IsFractionRing.of_field (⊥ : Subalgebra ℤ ℚ) ℚ fun z ↦ ⟨algebraMap ℤ _ z.num, algebraMap ℤ _ z.den, ?_⟩
    rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]
    simp [Rat.num_div_den]
  obtain ⟨m, hm, -⟩ := Ideal.exists_le_maximal (⊥ : Ideal (⊥ : Subalgebra ℤ ℚ)) bot_ne_top
  exact ⟨⊥, m, hft, hfr, hm⟩
end GroundTheory.Heights₂.Heights


