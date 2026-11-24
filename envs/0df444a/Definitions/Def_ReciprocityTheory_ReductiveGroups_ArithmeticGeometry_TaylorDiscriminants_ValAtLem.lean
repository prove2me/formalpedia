-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ValAtLem
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ValAtLem
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:57:57.415815+00:00
-- url     : https://prove2.me/theorems/85d7bacd-7072-4319-bd7d-a17f9d5b69dc
-- title:
--   Val At Lem
-- statement:
--   Definitions and structural lemmas for Val At Lem, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/ValAtLem.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsLieBasis
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_AnalyticForms_AnalyticCharts_Osgood
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
namespace ReciprocityTheory.ChartRestriction.G.TB.ValAt
open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Geo.Tor
variable {X : Scheme.{0}}
theorem valAt'_of (x : Sp ℂ ⟶ X) (U : X.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U) (f : Γ(X, U)) :
    valAt' x U f = valAt x U h f := dif_pos h
theorem valAt'_of_not (x : Sp ℂ ⟶ X) (U : X.Opens) (h : ¬ ⊤ ≤ x ⁻¹ᵁ U) (f : Γ(X, U)) : valAt' x U f = 0 :=
  dif_neg h
theorem valAt'_mul (x : Sp ℂ ⟶ X) (U : X.Opens) (f g : Γ(X, U)) :
    valAt' x U (f * g) = valAt' x U f * valAt' x U g := by
  by_cases h : ⊤ ≤ x ⁻¹ᵁ U
  · simp [valAt'_of _ _ h, valAt]
  · simp [valAt'_of_not _ _ h]
theorem valAt'_add (x : Sp ℂ ⟶ X) (U : X.Opens) (f g : Γ(X, U)) :
    valAt' x U (f + g) = valAt' x U f + valAt' x U g := by
  by_cases h : ⊤ ≤ x ⁻¹ᵁ U
  · simp [valAt'_of _ _ h, valAt]
  · simp [valAt'_of_not _ _ h]
theorem valAt'_one (x : Sp ℂ ⟶ X) (U : X.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U) : valAt' x U 1 = 1 := by
  simp [valAt'_of _ _ h, valAt]
def valHom (x : Sp ℂ ⟶ X) (U : X.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U) : Γ(X, U) →+* ℂ where
  toFun := valAt' x U
  map_one' := valAt'_one x U h
  map_mul' := valAt'_mul x U
  map_zero' := by simp [valAt'_of _ _ h, valAt]
  map_add' := valAt'_add x U
section Hol
open NumberField
variable {g : ℕ}
end Hol
section Periodic
variable {g : ℕ}
end Periodic
end ReciprocityTheory.ChartRestriction.G.TB.ValAt


