-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_SplitR
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_SplitR
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T15:43:41.775137+00:00
-- url     : https://prove2.me/theorems/2a18a8a7-3772-4cab-ac8c-f786ef0e60ef
-- title:
--   Split R
-- statement:
--   Definitions and structural lemmas for Split R, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/SplitR.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_SplitC
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_actE_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.ChartRestriction.G.I2.actE_apply


set_option autoImplicit false
namespace ReciprocityTheory.ChartRestriction.G.I2
open NumberField Complex
open scoped InnerProductSpace
noncomputable section
variable {E : Type} [Field E] [NumberField E]
section rk
variable {dim : (E →+* ℂ) → ℕ}
def rkFam {ρ : ℕ} (e : Fin ρ → Vsp dim) (p : Module.Free.ChooseBasisIndex ℤ (𝓞 E) × Fin ρ) :
    Vsp dim :=
  act (RingOfIntegers.basis E p.1) (e p.2)
def rkP (τ : E →+* ℂ) : Vsp dim →ₗ[ℂ] (Fin (dim τ) → ℂ) where
  toFun v a := v ⟨τ, a⟩
  map_add' v w := by ext a; simp
  map_smul' c v := by ext a; simp
open Classical in

def rkQ (τ : E →+* ℂ) : (Fin (dim τ) → ℂ) →ₗ[ℂ] Vsp dim where
  toFun y := ∑ a, y a • EuclideanSpace.single (⟨τ, a⟩ : Idx dim) (1 : ℂ)
  map_add' y z := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' c y := by simp [Finset.smul_sum, smul_smul]
end rk
end
end ReciprocityTheory.ChartRestriction.G.I2


