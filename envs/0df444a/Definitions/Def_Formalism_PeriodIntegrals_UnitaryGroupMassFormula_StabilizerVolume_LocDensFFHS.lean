-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerVolume_LocDensFFHS
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerVolume_LocDensFFHS
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T01:05:27.617809+00:00
-- url     : https://prove2.me/theorems/079625b4-f9c0-40bb-81ed-8ef71d0fc789
-- title:
--   Loc Dens FFHS
-- statement:
--   Definitions and structural lemmas for Loc Dens FFHS, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/StabilizerVolume/LocDensFFHS.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerVolume_LocDensFF
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PI.VolStabS.FFHS
open Module
variable {K : Type} [Field K] {σ : K →+* K}
structure IsSq {V : Type} [AddCommGroup V] [Module K V] (σ : K →+* K) (h : V → V → K) :
    Prop where
  add_right : ∀ x y z, h x (y + z) = h x y + h x z
  smul_right : ∀ (c : K) x y, h x (c • y) = c * h x y
  herm : ∀ x y, h y x = σ (h x y)
structure IsHS {V : Type} [AddCommGroup V] [Module K V] (σ : K →+* K) (h : V → V → K) : Prop
    extends IsSq σ h where
  nondeg : ∀ x, (∀ y, h x y = 0) → x = 0
section basic
variable {V : Type} [AddCommGroup V] [Module K V] {h : V → V → K}
def IsSq.lin (hs : IsSq σ h) (x : V) : V →ₗ[K] K where
  toFun := h x
  map_add' := hs.add_right x
  map_smul' c y := by simp [hs.smul_right]
def perp (hs : IsSq σ h) (e : V) : Submodule K V := LinearMap.ker (hs.lin e)
end basic
end PI.VolStabS.FFHS


