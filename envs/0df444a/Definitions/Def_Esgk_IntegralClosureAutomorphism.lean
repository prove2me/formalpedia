-- Prove2me | Definitions.Def_Esgk_IntegralClosureAutomorphism
-- name    : Esgk_IntegralClosureAutomorphism
-- status  : Definition
-- author  : @mysticflounder
-- created : 2026-10-16T04:43:51.489116+00:00
-- url     : https://prove2.me/theorems/708912c7-c4b5-4d0d-92ee-802eeec7bdf1
-- title:
--   Algebra isomorphisms on integral closures
-- statement:
--   This constructs the isomorphism induced on integral closures by a field algebra isomorphism and records preservation of integral elements.

-- Extracted dependency interfaces and their necessary proofs.
import Mathlib
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic

/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/


noncomputable section

namespace Esgk

variable {F A K : Type*}
variable [CommRing F] [CommRing A] [CommRing K]
variable [Algebra F K] [Algebra A K]


theorem isIntegral_algEquiv_apply_of_algebraMap_isIntegral
    (e : K ≃ₐ[F] K)
    (he : ∀ a : A, IsIntegral A (e (algebraMap A K a)))
    {x : K} (hx : IsIntegral A x) :
    IsIntegral A (e x) := by
  let φ : A →+* integralClosure A K :=
    ((e : K →+* K).comp (algebraMap A K)).codRestrict
      (integralClosure A K) (fun a => he a)
  have hφ :
      (algebraMap (integralClosure A K) K).comp φ =
        (e : K →+* K).comp (algebraMap A K) := by
    ext a
    rfl
  have hx' : IsIntegral (integralClosure A K) (e x) :=
    IsIntegral.map_of_comp_eq φ (e : K →+* K) hφ hx
  exact isIntegral_trans (e x) hx'


noncomputable def integralClosureAlgEquiv
    [Algebra F (integralClosure A K)]
    [IsScalarTower F (integralClosure A K) K]
    (e : K ≃ₐ[F] K)
    (hforward : ∀ a : A, IsIntegral A (e (algebraMap A K a)))
    (hbackward : ∀ a : A, IsIntegral A (e.symm (algebraMap A K a))) :
    integralClosure A K ≃ₐ[F] integralClosure A K := by
  let forward : integralClosure A K →ₐ[F] integralClosure A K :=
    { toFun := fun x =>
        ⟨e (x : K),
          isIntegral_algEquiv_apply_of_algebraMap_isIntegral
            e hforward x.property⟩
      map_one' := Subtype.ext e.map_one
      map_mul' := fun x y => Subtype.ext (e.map_mul x y)
      map_zero' := Subtype.ext e.map_zero
      map_add' := fun x y => Subtype.ext (e.map_add x y)
      commutes' := fun c => by
        apply Subtype.ext
        change e
            ((algebraMap (integralClosure A K) K)
              (algebraMap F (integralClosure A K) c)) =
          (algebraMap (integralClosure A K) K)
            (algebraMap F (integralClosure A K) c)
        rw [← IsScalarTower.algebraMap_apply F (integralClosure A K) K]
        exact e.commutes c }
  let backward : integralClosure A K →ₐ[F] integralClosure A K :=
    { toFun := fun x =>
        ⟨e.symm (x : K),
          isIntegral_algEquiv_apply_of_algebraMap_isIntegral
            e.symm hbackward x.property⟩
      map_one' := Subtype.ext e.symm.map_one
      map_mul' := fun x y => Subtype.ext (e.symm.map_mul x y)
      map_zero' := Subtype.ext e.symm.map_zero
      map_add' := fun x y => Subtype.ext (e.symm.map_add x y)
      commutes' := fun c => by
        apply Subtype.ext
        change e.symm
            ((algebraMap (integralClosure A K) K)
              (algebraMap F (integralClosure A K) c)) =
          (algebraMap (integralClosure A K) K)
            (algebraMap F (integralClosure A K) c)
        rw [← IsScalarTower.algebraMap_apply F (integralClosure A K) K]
        exact e.symm.commutes c }
  exact AlgEquiv.ofAlgHom forward backward
    (AlgHom.ext fun x => Subtype.ext (e.apply_symm_apply (x : K)))
    (AlgHom.ext fun x => Subtype.ext (e.symm_apply_apply (x : K)))


end Esgk


