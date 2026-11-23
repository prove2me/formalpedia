-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_HfRsmulRight
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_HfRsmulRight
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T15:34:11.730731+00:00
-- url     : https://prove2.me/theorems/1f717710-86e1-44f4-a4ff-6bdeb478678e
-- title:
--   Hf Rsmul Right
-- statement:
--   Definitions and structural lemmas for Hf Rsmul Right, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/HfRsmulRight.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_SplitSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GaussianTailBound
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.ChartRestriction.G.I2
open NumberField Complex
noncomputable section
variable {E : Type} [Field E] [NumberField E]
namespace ChA
open Classical in

def prj {dim : (E →+* ℂ) → ℕ} (σ : E →+* ℂ) : Vsp dim →ₗ[ℂ] Vsp dim where
  toFun v := WithLp.toLp 2 fun i => if i.1 = σ then v i else 0
  map_add' v w := by ext i; simp only [PiLp.add_apply]; split_ifs <;> simp
  map_smul' c v := by ext i; simp only [PiLp.smul_apply, smul_eq_mul, RingHom.id_apply]; split_ifs <;> simp
open Classical in

def Mc {dim : (E →+* ℂ) → ℕ} (σ : E →+* ℂ) (c : ℂ) : Vsp dim →ₗ[ℂ] Vsp dim where
  toFun v := WithLp.toLp 2 fun i => if i.1 = σ then c * v i else
    if i.1 = ComplexEmbedding.conjugate σ then (starRingEnd ℂ) c * v i else 0
  map_add' v w := by ext i; simp only [PiLp.add_apply]; split_ifs <;> ring
  map_smul' a v := by ext i; simp only [PiLp.smul_apply, smul_eq_mul, RingHom.id_apply]; split_ifs <;> ring
end ChA
end
end ReciprocityTheory.ChartRestriction.G.I2


