-- Prove2me | Definitions.Def_GroundTheory_ProfiniteCohomology_CharactersDefs
-- name    : GroundTheory_ProfiniteCohomology_CharactersDefs
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T06:08:47.297895+00:00
-- url     : https://prove2.me/theorems/eb3763c2-2587-441a-9c86-923fbf7904a3
-- title:
--   Characters Defs
-- statement:
--   Definitions and structural lemmas for Characters Defs, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/CharactersDefs.lean

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_TorsionDualDefs
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.ProfCoh
section LocallyConstantHom
variable (G : Type*) [Group G] [TopologicalSpace G] (M : Type*) [AddCommGroup M]
def locallyConstantHom : AddSubgroup (Additive G →+ M) where
  carrier := {χ | IsLocallyConstant fun g : G => χ (Additive.ofMul g)}
  zero_mem' := by
    change IsLocallyConstant fun g : G => (0 : Additive G →+ M) (Additive.ofMul g)
    exact IsLocallyConstant.const (0 : M)
  add_mem' {χ ψ} hχ hψ := by
    change IsLocallyConstant fun g : G => (χ + ψ) (Additive.ofMul g)
    exact IsLocallyConstant.add hχ hψ
  neg_mem' {χ} hχ := by
    change IsLocallyConstant fun g : G => (-χ) (Additive.ofMul g)
    exact IsLocallyConstant.neg hχ
def locallyConstantHomQZEquiv : locallyConstantHom G (AddCircle (1 : ℚ)) ≃+ (Additive G →ₜ+ QZ) where
  toFun χ :=
    { toAddMonoidHom := QZ.toAddCircle.symm.toAddMonoidHom.comp χ.1
      continuous_toFun := (IsLocallyConstant.iff_continuous _).1 χ.2 }
  invFun χ := ⟨QZ.toAddCircle.toAddMonoidHom.comp χ.toAddMonoidHom,
    (IsLocallyConstant.iff_continuous (fun x : Additive G => χ x)).2 χ.continuous⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
end LocallyConstantHom
end GroundTheory.ProfCoh


