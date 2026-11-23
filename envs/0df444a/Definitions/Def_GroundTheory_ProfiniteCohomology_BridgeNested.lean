-- Prove2me | Definitions.Def_GroundTheory_ProfiniteCohomology_BridgeNested
-- name    : GroundTheory_ProfiniteCohomology_BridgeNested
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T09:53:05.222577+00:00
-- url     : https://prove2.me/theorems/988596de-1d69-446a-936f-6e2b85a7931d
-- title:
--   Bridge Nested
-- statement:
--   Definitions and structural lemmas for Bridge Nested, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/BridgeNested.lean

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
open CategoryTheory TopRep ContRepresentation
universe u v w
section Cons
variable {G : Type v} [TopologicalSpace G]
def finConsHomeomorph (m : ℕ) : G × (Fin m → G) ≃ₜ (Fin (m + 1) → G) where
  toFun p := Fin.cons p.1 p.2
  invFun x := (x 0, Fin.tail x)
  left_inv p := by simp
  right_inv x := by simp
  continuous_toFun := Continuous.finCons (A := fun _ : Fin (m + 1) => G) continuous_fst continuous_snd
  continuous_invFun := (continuous_apply 0).prodMk (continuous_pi fun _ => continuous_apply _)
@[simp]
theorem finConsHomeomorph_symm_apply (m : ℕ) (x : Fin (m + 1) → G) :
    (finConsHomeomorph m).symm x = (x 0, Fin.tail x) :=
  rfl
end Cons
variable {k G : Type u} [Ring k] [TopologicalSpace k] [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] [LocallyCompactSpace G]
def nestedHomeomorph (X : TopRep.{u} k G) : (m : ℕ) → resolutionX X m ≃ₜ C(Fin m → G, X)
  | 0 => Homeomorph.continuousMapOfUnique
  | m + 1 => ((Homeomorph.refl G).arrowCongr (nestedHomeomorph X m)).trans
      (Homeomorph.curry.symm.trans ((finConsHomeomorph m).arrowCongr (Homeomorph.refl X)))
variable (X : TopRep.{u} k G)
@[simp]
theorem nestedHomeomorph_zero_apply (v : resolutionX X 0) (x : Fin 0 → G) :
    nestedHomeomorph X 0 v x = v :=
  rfl
theorem nestedHomeomorph_add (m : ℕ) (a b : resolutionX X m) :
    nestedHomeomorph X m (a + b) = nestedHomeomorph X m a + nestedHomeomorph X m b := by
  induction m with
  | zero => ext x; rfl
  | succ m ih =>
    ext x
    change nestedHomeomorph X m (((a + b : resolutionX X (m + 1)) : C(G, resolutionX X m)) (x 0))
        (Fin.tail x) = nestedHomeomorph X m ((a : C(G, resolutionX X m)) (x 0)) (Fin.tail x) +
          nestedHomeomorph X m ((b : C(G, resolutionX X m)) (x 0)) (Fin.tail x)
    rw [ContinuousMap.add_apply, ih]
    rfl
theorem nestedHomeomorph_smul (m : ℕ) (r : k) (a : resolutionX X m) :
    nestedHomeomorph X m (r • a) = r • nestedHomeomorph X m a := by
  induction m with
  | zero => ext x; rfl
  | succ m ih =>
    ext x
    change nestedHomeomorph X m (((r • a : resolutionX X (m + 1)) : C(G, resolutionX X m)) (x 0))
        (Fin.tail x) = r • nestedHomeomorph X m ((a : C(G, resolutionX X m)) (x 0)) (Fin.tail x)
    rw [ContinuousMap.smul_apply, ih]
    rfl
def nestedLinearEquiv (m : ℕ) : resolutionX X m ≃ₗ[k] C(Fin m → G, X) where
  toFun := nestedHomeomorph X m
  invFun := (nestedHomeomorph X m).symm
  map_add' := nestedHomeomorph_add X m
  map_smul' := nestedHomeomorph_smul X m
  left_inv := (nestedHomeomorph X m).symm_apply_apply
  right_inv := (nestedHomeomorph X m).apply_symm_apply
end GroundTheory.ProfCoh


