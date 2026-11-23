-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_FiniteFaithfullyFlatKer
-- name    : Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_FiniteFaithfullyFlatKer
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T03:32:31.362017+00:00
-- url     : https://prove2.me/theorems/18006aed-347f-48fc-8253-66c67b11b92c
-- title:
--   Finite Faithfully Flat Ker
-- statement:
--   Definitions and structural lemmas for Finite Faithfully Flat Ker, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/FiniteFaithfullyFlatKer.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace GlobalTheory.HopfQuot
open TensorProduct
section Trace
variable {A M ι : Type*} [CommRing A] [AddCommGroup M] [Module A M] [Fintype ι]
def tr (e : ι → M) (c : ι → M →ₗ[A] A) (φ : M →ₗ[A] M) : A := ∑ i, c i (φ (e i))
end Trace
section Ev
variable {R Λ : Type*} [CommRing R] [AddCommGroup Λ] [Module R Λ]
noncomputable def ev (B : Type*) [CommRing B] [Algebra R B] (f : Λ →ₗ[R] R) :
    B ⊗[R] Λ →ₗ[B] B :=
  (TensorProduct.AlgebraTensorModule.rid R B B).toLinearMap ∘ₗ f.baseChange B
end Ev
section Integral
variable {R Λ ι : Type*} [CommRing R] [CommRing Λ] [HopfAlgebra R Λ] [Fintype ι]
noncomputable def hit (f : Λ →ₗ[R] R) : Λ →ₗ[R] Λ :=
  (ev Λ f).restrictScalars R ∘ₗ Coalgebra.comul
noncomputable def shear (R Λ : Type*) [CommRing R] [CommRing Λ] [HopfAlgebra R Λ] :
    Λ ⊗[R] Λ →ₐ[Λ] Λ ⊗[R] Λ :=
  Algebra.TensorProduct.lift (Algebra.ofId Λ _) (Bialgebra.comulAlgHom R Λ)
    (fun _ _ => Commute.all _ _)
noncomputable def lam (e : ι → Λ) (c : ι → Λ →ₗ[R] R) (f : Λ →ₗ[R] R) : Λ →ₗ[R] R :=
  ∑ i, c i ∘ₗ hit f ∘ₗ LinearMap.mulRight R (e i)
end Integral
section Action
variable {R Λ B : Type*} [CommRing R] [CommRing Λ] [HopfAlgebra R Λ] [CommRing B] [Algebra R B]
  (ρ : B →ₐ[R] B ⊗[R] Λ)
end Action
end GlobalTheory.HopfQuot
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory


