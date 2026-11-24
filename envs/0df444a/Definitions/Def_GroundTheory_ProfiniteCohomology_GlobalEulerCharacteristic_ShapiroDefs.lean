-- Prove2me | Definitions.Def_GroundTheory_ProfiniteCohomology_GlobalEulerCharacteristic_ShapiroDefs
-- name    : GroundTheory_ProfiniteCohomology_GlobalEulerCharacteristic_ShapiroDefs
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T22:52:24.070034+00:00
-- url     : https://prove2.me/theorems/f3783b8a-d950-4f0b-a476-0a37913912c3
-- title:
--   Shapiro Defs
-- statement:
--   Definitions and structural lemmas for Shapiro Defs, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/GlobalEulerCharacteristic/ShapiroDefs.lean

import Mathlib
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
universe u
variable {k G V : Type*} [CommRing k] [Group G] [AddCommGroup V] [Module k V]
def funDiagRepresentation (X : Type*) [MulAction G X] (ρ : Representation k G V) :
    Representation k G (X → V) where
  toFun g :=
    { toFun := fun F x => ρ g (F (g⁻¹ • x))
      map_add' := fun F F' => funext fun x => map_add (ρ g) _ _
      map_smul' := fun c F => funext fun x => map_smul (ρ g) c _ }
  map_one' := by
    refine LinearMap.ext fun F => funext fun x => ?_
    simp
  map_mul' g h := by
    refine LinearMap.ext fun F => funext fun x => ?_
    simp [mul_smul]
abbrev funDiagRep {k G : Type u} [CommRing k] [Group G] (X : Type u) [MulAction G X]
    (A : Rep.{u} k G) : Rep.{u} k G :=
  Rep.of (funDiagRepresentation X A.ρ)
end GroundTheory.ProfCoh


