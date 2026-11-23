-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusSplitting_EqTopOfForallEmbAllMem
-- name    : Development_AbelianVarietyTheory_Proofs_TorusSplitting_EqTopOfForallEmbAllMem
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T11:22:22.593825+00:00
-- url     : https://prove2.me/theorems/0687c748-d2e4-45bc-9312-91ae19647be8
-- title:
--   Eq Top Of Forall Emb All Mem
-- statement:
--   Definitions and structural lemmas for Eq Top Of Forall Emb All Mem, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusSplitting/EqTopOfForallEmbAllMem.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_TorusAtData
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.I2
namespace GlobalTheory.CMLattice
noncomputable section
variable {E : Type} [Field E] [NumberField E]
def embAll (Ψ : Finset (E →+* ℂ)) (r : ℕ) : (Fin r → E) →ₗ[ℤ] (Ψ → Fin r → ℂ) :=
  AddMonoidHom.toIntLinearMap
    { toFun := fun v τ a => τ.1 (v a)
      map_zero' := by ext; simp
      map_add' := by intros; ext; simp }
end
end GlobalTheory.CMLattice


