-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_IsOfFinOrderOfBounded
-- name    : Development_AbelianVarietyTheory_Proofs_UnitaryExistence_IsOfFinOrderOfBounded
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T07:03:02.037877+00:00
-- url     : https://prove2.me/theorems/32cb91dd-c7a2-4762-ba86-fa66aadfcce7
-- title:
--   Is Of Fin Order Of Bounded
-- statement:
--   Definitions and structural lemmas for Is Of Fin Order Of Bounded, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/IsOfFinOrderOfBounded.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_ProdCastLESucc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_ExistsIntMulIntegral
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_BoundedPowOfTriangularIsometry
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Matrix
open scoped nonZeroDivisors ComplexConjugate
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
namespace GlobalTheory.GamFree
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
omit [IsCMField E] in

noncomputable def restrict (Λ : Submodule (𝓞 E) (Fin r → E)) (γ : GL (Fin r) E)
    (hγ : ∀ v, v ∈ Λ ↔ (γ : Matrix (Fin r) (Fin r) E) *ᵥ v ∈ Λ) : Λ ≃ₗ[ℤ] Λ where
  toFun v := ⟨(γ : Matrix (Fin r) (Fin r) E) *ᵥ v, (hγ _).1 v.2⟩
  invFun v := ⟨((γ⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) *ᵥ v, (hγ _).2 (by
    rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]; exact v.2)⟩
  map_add' v w := Subtype.ext (Matrix.mulVec_add (γ : Matrix (Fin r) (Fin r) E) (v : Fin r → E) w)
  map_smul' c v := Subtype.ext (Matrix.mulVec_smul (γ : Matrix (Fin r) (Fin r) E) c (v : Fin r → E))
  left_inv v := Subtype.ext (by
    simp only [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec])
  right_inv v := Subtype.ext (by
    simp only [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec])
end GlobalTheory.GamFree


