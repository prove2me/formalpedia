-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_ChartPSmulLiftEqBt
-- name    : Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_ChartPSmulLiftEqBt
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T15:36:32.361093+00:00
-- url     : https://prove2.me/theorems/4202fe16-d334-4ce7-9c35-905d4fc4942d
-- title:
--   Chart PSmul Lift Eq Bt
-- statement:
--   Definitions and structural lemmas for Chart PSmul Lift Eq Bt, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/ChartPSmulLiftEqBt.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_EvBtStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open TensorProduct IsLocalRing Matrix ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Be2
namespace GlobalTheory
section
variable {R₀ : Type} [CommRing R₀] {g : ℕ} {V : Type} [AddCommGroup V] [Module R₀ V]
def btTanCrd (gb : Module.Basis (Fin g) R₀ V) (M : Type) [AddCommGroup M] [Module R₀ M]
    (k : Fin g) : V ⊗[R₀] M →ₗ[R₀] M :=
  (TensorProduct.lid R₀ M).toLinearMap ∘ₗ LinearMap.rTensor M (gb.coord k)
end
end GlobalTheory


