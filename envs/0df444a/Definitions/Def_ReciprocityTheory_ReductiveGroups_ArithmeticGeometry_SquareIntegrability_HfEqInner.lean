-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_HfEqInner
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_HfEqInner
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T15:34:27.548579+00:00
-- url     : https://prove2.me/theorems/6e84a5e1-2231-4999-bf10-97bde0f08b79
-- title:
--   Hf Eq Inner
-- statement:
--   Definitions and structural lemmas for Hf Eq Inner, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/HfEqInner.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_SplitSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_LemmaS
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
def VP {dim : (E →+* ℂ) → ℕ} (σ : E →+* ℂ) : Submodule ℂ (Vsp dim) where
  carrier := {v | InPart σ v}
  add_mem' := fun {a b} ha hb j hj => by simp [ha j hj, hb j hj]
  zero_mem' := fun j _ => rfl
  smul_mem' := fun c v hv j hj => by simp [hv j hj]
open Classical in

def prj {dim : (E →+* ℂ) → ℕ} (σ : E →+* ℂ) (v : Vsp dim) : Vsp dim :=
  WithLp.toLp 2 fun j => if j.1 = σ then v j else 0
def mulc {dim : (E →+* ℂ) → ℕ} (c : (E →+* ℂ) → ℂ) (v : Vsp dim) : Vsp dim :=
  WithLp.toLp 2 fun j => c j.1 * v j
end
end ReciprocityTheory.ChartRestriction.G.I2


