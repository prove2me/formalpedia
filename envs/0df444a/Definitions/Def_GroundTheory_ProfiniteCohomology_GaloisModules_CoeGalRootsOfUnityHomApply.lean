-- Prove2me | Definitions.Def_GroundTheory_ProfiniteCohomology_GaloisModules_CoeGalRootsOfUnityHomApply
-- name    : GroundTheory_ProfiniteCohomology_GaloisModules_CoeGalRootsOfUnityHomApply
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T05:06:50.130198+00:00
-- url     : https://prove2.me/theorems/4bd11dec-dd75-43cf-b804-002f64227663
-- title:
--   Coe Gal Roots Of Unity Hom Apply
-- statement:
--   Definitions and structural lemmas for Coe Gal Roots Of Unity Hom Apply, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/GaloisModules/CoeGalRootsOfUnityHomApply.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace GroundTheory.ProfCoh
universe w u v
section IntRep
variable {G : Type v} [Monoid G]
def intRep {V : Type u} [AddCommGroup V] (φ : G →* AddMonoid.End V) :
    Representation (ULift.{w} ℤ) G V where
  toFun g :=
    { toFun := φ g
      map_add' := map_add (φ g)
      map_smul' := fun r x => by
        change φ g (r.down • x) = r.down • φ g x
        exact map_zsmul (φ g) r.down x }
  map_one' := by
    ext x
    simp
  map_mul' g h := by
    ext x
    simp
@[simp]
theorem intRep_apply {V : Type u} [AddCommGroup V] (φ : G →* AddMonoid.End V) (g : G) (x : V) :
    intRep.{w} φ g x = φ g x :=
  rfl
def intRepOfMonoidEnd {M : Type u} [CommGroup M] (φ : G →* Monoid.End M) :
    Representation (ULift.{w} ℤ) G (Additive M) :=
  intRep.{w} ((monoidEndToAdditive M : Monoid.End M →* AddMonoid.End (Additive M)).comp φ)
@[simp]
theorem intRepOfMonoidEnd_apply {M : Type u} [CommGroup M] (φ : G →* Monoid.End M) (g : G)
    (x : Additive M) :
    intRepOfMonoidEnd.{w} φ g x = Additive.ofMul (φ g x.toMul) :=
  rfl
def zRepOfMonoidEnd {M : Type u} [CommGroup M] (φ : G →* Monoid.End M) :
    Representation ℤ G (Additive M) :=
  (addMonoidEndRingEquivInt (Additive M) : AddMonoid.End (Additive M) →* _).comp
    ((monoidEndToAdditive M : Monoid.End M →* AddMonoid.End (Additive M)).comp φ)
@[simp]
theorem zRepOfMonoidEnd_apply {M : Type u} [CommGroup M] (φ : G →* Monoid.End M) (g : G)
    (x : Additive M) :
    zRepOfMonoidEnd φ g x = Additive.ofMul (φ g x.toMul) :=
  rfl
end IntRep
section Galois
variable (K : Type*) (L : Type u) [Field K] [Field L] [Algebra K L]
def galUnitsHom : Gal(L/K) →* Monoid.End Lˣ where
  toFun σ := Units.map (σ : L →* L)
  map_one' := by
    ext u
    rfl
  map_mul' σ τ := by
    ext u
    rfl
@[simp]
theorem coe_galUnitsHom_apply (σ : Gal(L/K)) (u : Lˣ) :
    ((galUnitsHom K L σ u : Lˣ) : L) = σ u :=
  rfl
def galRootsOfUnityHom (n : ℕ) : Gal(L/K) →* Monoid.End (rootsOfUnity n L) where
  toFun σ := restrictRootsOfUnity σ n
  map_one' := by
    ext ζ
    rfl
  map_mul' σ τ := by
    ext ζ
    rfl
abbrev galAdd : Rep.{u} K Gal(L/K) := Rep.ofDistribMulAction K Gal(L/K) L
abbrev galAddInt : Rep.{u} (ULift.{w} ℤ) Gal(L/K) :=
  Rep.of (intRep.{w} (DistribMulAction.toAddMonoidEnd Gal(L/K) L))
abbrev galUnits : Rep.{u} (ULift.{w} ℤ) Gal(L/K) :=
  Rep.of (intRepOfMonoidEnd.{w} (galUnitsHom K L))
abbrev galRootsOfUnity (n : ℕ) : Rep.{u} (ULift.{w} ℤ) Gal(L/K) :=
  Rep.of (intRepOfMonoidEnd.{w} (galRootsOfUnityHom K L n))
abbrev galAddZ : Rep.{u} ℤ Gal(L/K) := Rep.ofDistribMulAction ℤ Gal(L/K) L
abbrev galUnitsZ : Rep.{u} ℤ Gal(L/K) := Rep.of (zRepOfMonoidEnd (galUnitsHom K L))
abbrev galRootsOfUnityZ (n : ℕ) : Rep.{u} ℤ Gal(L/K) :=
  Rep.of (zRepOfMonoidEnd (galRootsOfUnityHom K L n))
variable {K L}
end Galois
end GroundTheory.ProfCoh


