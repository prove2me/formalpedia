-- Prove2me | solution 1 for AlgebraicGeometry.OModulePresheaf.exists_finite_euler_quotient_of_isProper
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-10-11T13:49:37.797259+00:00
-- url     : https://prove2.me/submissions/370d9152-e975-41aa-88a3-7fc38d2803a6
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_AlgebraicGeometry_RelPicard_exists_finite_algEquiv_quotient_of_isProper
import Theorems.Thm_AlgebraicGeometry_RelPicard_IsAlgEquivZero_eulerChar_pullback_tensor_eq_monoidalV2
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_nonempty_cechEquiv_ofModules_of_iso

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open AlgebraicGeometry CategoryTheory MonoidalCategory
universe u

namespace PhilipponMultiplicity.SchemeEuler
variable {K : Type u} [Field K] {X : Scheme.{u}} (π : X ⟶ Spec (.of K))

theorem euler_iso {M N : X.Modules} (e : M ≅ N) (U : X.OrderedAffineCover) :
    (OModulePresheaf.ofModules π M).eulerChar U =
      (OModulePresheaf.ofModules π N).eulerChar U := by
  obtain ⟨⟨e0⟩, hS, -⟩ := OModulePresheaf.nonempty_cechEquiv_ofModules_of_iso π e U
  have h : ∀ i, (OModulePresheaf.ofModules π M).cechFinrank U i =
      (OModulePresheaf.ofModules π N).cechFinrank U i := by
    intro i
    cases i with
    | zero => exact e0.finrank_eq
    | succ j => obtain ⟨e⟩ := hS j; exact e.finrank_eq
  rw [OModulePresheaf.eulerChar_def, OModulePresheaf.eulerChar_def]
  exact Finset.sum_congr rfl fun i _ => by rw [h i]

end PhilipponMultiplicity.SchemeEuler

theorem solution
    (K : Type u) [Field K] [IsAlgClosed K] {X : Scheme.{u}}
    (π : X ⟶ Spec (.of K)) [IsProper π]
    (L : Type u) [AddCommGroup L] [Module ℤ L]
    (φ : Multiplicative L →* Skeleton X.Modules)
    (ℓ : L → X.Modules) (hℓ : ∀ l, Scheme.Modules.IsInvertible (ℓ l))
    (hclass : ∀ l, toSkeleton (ℓ l) = φ (Multiplicative.ofAdd l)) :
    ∃ (A : Type) (_ : AddCommGroup A) (_ : Module ℤ A) (_ : Module.Finite ℤ A)
      (q : L →ₗ[ℤ] A), Function.Surjective q ∧
      ∀ x y, q x = q y → ∀ (Y : Scheme.{u}) (f : Y ⟶ X), IsClosedImmersion f →
        ∀ U : Y.OrderedAffineCover,
          (OModulePresheaf.ofModules (f ≫ π) ((Scheme.Modules.pullback f).obj (ℓ x))).eulerChar U =
          (OModulePresheaf.ofModules (f ≫ π) ((Scheme.Modules.pullback f).obj (ℓ y))).eulerChar U := by
  obtain ⟨A, instA, modA, finA, q, hq, he⟩ :=
    RelPicard.exists_finite_algEquiv_quotient_of_isProper K π L φ ℓ hℓ hclass
  letI := instA
  letI := modA
  letI := finA
  refine ⟨A, instA, modA, finA, q, hq, ?_⟩
  intro x y hxy Y f hf U
  letI := hf
  obtain ⟨N, hN, hN0, ⟨e⟩⟩ := he x y hxy
  exact (PhilipponMultiplicity.SchemeEuler.euler_iso (f ≫ π)
      ((Scheme.Modules.pullback f).mapIso e) U).trans
    (RelPicard.IsAlgEquivZero.eulerChar_pullback_tensor_eq_monoidalV2
      π N (ℓ y) hN (hℓ y) hN0 f U)
