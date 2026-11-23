-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_BijectiveTensorOmegaStd
-- name    : Development_AbelianVarietyTheory_Proofs_ModuliProofs_BijectiveTensorOmegaStd
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T12:16:20.890807+00:00
-- url     : https://prove2.me/theorems/efb9a6dc-13c8-4cf9-b031-a94cae61f94f
-- title:
--   Bijective Tensor Omega Std
-- statement:
--   Definitions and structural lemmas for Bijective Tensor Omega Std, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/BijectiveTensorOmegaStd.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_MulVecOfRealVecAddMemSpanPeriodLattice
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.PTheta Matrix
open scoped Kronecker
noncomputable section
namespace GlobalTheory.TensorSiegel
section General
variable {ι : Type*} [Fintype ι]
end General
section Kron
variable {r h g : ℕ} (σ : Fin r × Fin h ≃ Fin g) {R : Type*} [CommRing R]
def kron (S : Matrix (Fin r) (Fin r) R) (P : Matrix (Fin h) (Fin h) R) :
    Matrix (Fin g) (Fin g) R := (S ⊗ₖ P).submatrix σ.symm σ.symm
def coordFst (x : Fin r → (Fin h ⊕ Fin h → ℤ)) : Fin g → ℤ :=
  fun k => x (σ.symm k).1 (.inl (σ.symm k).2)
def coordSnd (x : Fin r → (Fin h ⊕ Fin h → ℤ)) : Fin g → ℤ :=
  fun k => x (σ.symm k).1 (.inr (σ.symm k).2)
def period (τ : Matrix (Fin h) (Fin h) ℂ) : (Fin r → (Fin h ⊕ Fin h → ℤ)) →+ (Fin g → ℂ) :=
  AddMonoidHom.mk' (fun x => kron σ 1 τ *ᵥ ofIntVec (coordFst σ x) + ofIntVec (coordSnd σ x)) (by
    intro x y
    have e1 : coordFst σ (x + y) = coordFst σ x + coordFst σ y := rfl
    have e2 : coordSnd σ (x + y) = coordSnd σ x + coordSnd σ y := rfl
    simp only [e1, e2, ofIntVec_add, mulVec_add]
    abel)
def formMatrix (S : Matrix (Fin r) (Fin r) ℝ) (τ : Matrix (Fin h) (Fin h) ℂ) :
    Matrix (Fin g) (Fin g) ℂ := (kron σ S (τ.map Complex.im)⁻¹).map Complex.ofReal
def endo (a : Matrix (Fin r) (Fin r) ℤ) : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ) :=
  ((kron σ (a.map (Int.cast : ℤ → ℝ)) 1).map Complex.ofReal).mulVecLin
end Kron
end GlobalTheory.TensorSiegel
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
namespace GlobalTheory.TensorSiegel
end GlobalTheory.TensorSiegel


