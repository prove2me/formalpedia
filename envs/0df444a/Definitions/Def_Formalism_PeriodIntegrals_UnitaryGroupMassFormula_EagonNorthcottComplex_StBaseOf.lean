-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_EagonNorthcottComplex_StBaseOf
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_EagonNorthcottComplex_StBaseOf
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T05:05:16.620612+00:00
-- url     : https://prove2.me/theorems/78b0df03-9a53-4f11-8e14-2834c3c2f7be
-- title:
--   St Base Of
-- statement:
--   Definitions and structural lemmas for St Base Of, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/EagonNorthcottComplex/StBaseOf.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_EagonNorthcottComplex_StSpecOf
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
noncomputable section
namespace PIW.ENSpec
open PI.EagonNorthcott MvPolynomial TensorProduct
def phiS (R : Type u) [CommRing R] (D : ℕ) : R ⊗[ℤ] MvPolynomial (Fin D) ℤ ≃ₗ[ℤ] MvPolynomial (Fin D) R :=
  (MvPolynomial.algebraTensorAlgEquiv ℤ R).toLinearEquiv.restrictScalars ℤ
def phiV (R : Type u) [CommRing R] (D m : ℕ) :
    R ⊗[ℤ] (Fin m → MvPolynomial (Fin D) ℤ) ≃ₗ[ℤ] (Fin m → MvPolynomial (Fin D) R) :=
  (TensorProduct.piRight ℤ ℤ R (fun _ : Fin m => MvPolynomial (Fin D) ℤ)).trans
    (LinearEquiv.piCongrRight fun _ => phiS R D)
def BTens : Prop :=
  ∀ (A B C : Type) [AddCommGroup A] [AddCommGroup B] [AddCommGroup C] (f : A →ₗ[ℤ] B) (g : B →ₗ[ℤ] C),
    Function.Exact f g → Module.Flat ℤ (C ⧸ LinearMap.range g) →
      ∀ (R : Type u) [AddCommGroup R], Function.Exact (f.lTensor R) (g.lTensor R)
def BFlatKer : Prop :=
  ∀ (L M N : Type) [AddCommGroup L] [AddCommGroup M] [AddCommGroup N] (g : L →ₗ[ℤ] M) (h : M →ₗ[ℤ] N),
    Function.Exact g h → Module.IsTorsionFree ℤ N → Module.Flat ℤ (M ⧸ LinearMap.range g)
def BFlat0 : Prop :=
  ∀ (D m : ℕ) (e : Fin m → Fin D → ℕ),
    Module.Flat ℤ (MvPolynomial (Fin D) ℤ ⧸
      LinearMap.range ((aug (MvPolynomial.X : Fin D → MvPolynomial (Fin D) ℤ) e).restrictScalars ℤ))
def BCommD : Prop :=
  ∀ (R : Type u) [CommRing R] (D k l : ℕ) (C : Matrix (Fin k) (Fin l) (Fin D → ℤ)),
    (dmap (MvPolynomial.X : Fin D → MvPolynomial (Fin D) R) C).restrictScalars ℤ ∘ₗ (phiV R D l).toLinearMap =
      (phiV R D k).toLinearMap ∘ₗ ((dmap (MvPolynomial.X : Fin D → MvPolynomial (Fin D) ℤ) C).restrictScalars ℤ).lTensor R
def BCommA : Prop :=
  ∀ (R : Type u) [CommRing R] (D m : ℕ) (e : Fin m → Fin D → ℕ),
    (aug (MvPolynomial.X : Fin D → MvPolynomial (Fin D) R) e).restrictScalars ℤ ∘ₗ (phiV R D m).toLinearMap =
      (phiS R D).toLinearMap ∘ₗ ((aug (MvPolynomial.X : Fin D → MvPolynomial (Fin D) ℤ) e).restrictScalars ℤ).lTensor R
def BRange : Prop :=
  ∀ (R : Type u) [CommRing R] (D a m : ℕ) (e : Fin m → Fin D → ℕ),
    LinearMap.range (aug (MvPolynomial.X : Fin D → MvPolynomial (Fin D) ℤ) e) =
        Ideal.span (Set.range (MvPolynomial.X : Fin D → MvPolynomial (Fin D) ℤ)) ^ a →
      LinearMap.range (aug (MvPolynomial.X : Fin D → MvPolynomial (Fin D) R) e) =
        Ideal.span (Set.range (MvPolynomial.X : Fin D → MvPolynomial (Fin D) R)) ^ a
end PIW.ENSpec


