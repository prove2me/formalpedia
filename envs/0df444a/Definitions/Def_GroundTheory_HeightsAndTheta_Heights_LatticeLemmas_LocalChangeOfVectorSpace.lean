-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_LocalChangeOfVectorSpace
-- name    : GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_LocalChangeOfVectorSpace
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-25T09:38:57.392799+00:00
-- url     : https://prove2.me/theorems/12b3f2b1-52c8-5986-8ab0-27b5b8f4de86
-- title:
--   Local Change Of Vector Space
-- statement:
--   Definitions and structural lemmas for Local Change Of Vector Space, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LatticeLemmas/LocalChangeOfVectorSpace.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_PLocalChange
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_LatticeOfLocalisationsHyps
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.LatticeLemmas
open NumberField NumberField.ComplexEmbedding TensorProduct IsDedekindDomain
  GroundTheory.Heights₂.Heights.ComplexAt
universe u v
noncomputable section
set_option linter.unusedSectionVars false
namespace LocalChangeEq
def AAt (K : Type*) [Field K] [NumberField K] (V : Type*) [AddCommGroup V] [Module K V]
    [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] : Prop :=
  ∀ (Nm : HermitianNorms K V) (M₁ M₂ : FullLattice K V)
    (g : ∀ v : HeightOneSpectrum (𝓞 K),
      (v.adicCompletion K ⊗[K] V) ≃ₗ[v.adicCompletion K] (v.adicCompletion K ⊗[K] V)),
    {v | g v ≠ 1}.Finite →
    (∀ v, (Heights.localLattice v M₂.carrier : Set (v.adicCompletion K ⊗[K] V)) =
      g v '' Heights.localLattice v M₁.carrier) →
      (Nm.bundle M₂).deg = (Nm.bundle M₁).deg +
        (∑ᶠ v, Real.log ‖LinearMap.det
          ((g v : (v.adicCompletion K ⊗[K] V) →ₗ[v.adicCompletion K] (v.adicCompletion K ⊗[K] V)))‖) /
          Module.finrank ℚ K
def BAt (K : Type*) [Field K] [NumberField K] (r : ℕ) : Prop :=
  ∀ (H : HermitianSpace K r)
    (M₁ M₂ : Submodule (𝓞 K) (Fin r → K)) (h₁ : IsLattice M₁) (h₂ : IsLattice M₂)
    (g : ∀ v : HeightOneSpectrum (𝓞 K), Matrix.GeneralLinearGroup (Fin r) (v.adicCompletion K)),
    {v | g v ≠ 1}.Finite →
    (∀ v, localLattice v M₂ = (localLattice v M₁).map (glMap v (g v))) →
    deg (H.lattice M₂ h₂.1) = deg (H.lattice M₁ h₁.1) +
      (∑ᶠ v, Real.log ‖(g v : Matrix (Fin r) (Fin r) (v.adicCompletion K)).det‖) /
        Module.finrank ℚ K
variable {K : Type*} [Field K] [NumberField K]
theorem coordMap_coordInv (r : ℕ) (σ : K →+* ℂ) (w : Fin r → ℂ) :
    coordMap r σ (coordInv σ w) = w := by
  funext j
  simp only [coordInv, map_sum, Finset.sum_apply, coordMap_tmul, AlgEquiv.symm_apply_apply,
    Pi.single_apply]
  simp
theorem coordMap_conjMap (r : ℕ) (σ : K →+* ℂ) (t : Fibre σ (Fin r → K)) :
    coordMap r (conjugate σ) (conjMap σ (Fin r → K) t) = star (coordMap r σ t) := by
  induction t using TensorProduct.induction_on with
  | zero => simp only [map_zero, star_zero]
  | tmul z l =>
    ext i
    rw [conjMap_tmul]
    change coordMap r (conjugate σ) (conj σ z ⊗ₜ l) i = starRingEnd ℂ (coordMap r σ (z ⊗ₜ l) i)
    rw [coordMap_tmul, coordMap_tmul, map_mul]
    rfl
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, star_add]
variable {V : Type*} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
variable {r : ℕ} (φ : V ≃ₗ[K] (Fin r → K))
def intEquiv : V ≃ₗ[𝓞 K] (Fin r → K) := φ.restrictScalars (𝓞 K)
def fibreCoord (σ : K →+* ℂ) : Fibre σ V →ₗ[ℂ] (Fin r → ℂ) :=
  coordMap r σ ∘ₗ fibreMap σ (intEquiv φ).toLinearMap
theorem fibreCoord_bijective (σ : K →+* ℂ) : Function.Bijective (fibreCoord φ σ) := by
  refine ⟨(coordMap_injective σ).comp (fibreMap_injective σ (intEquiv φ).injective), ?_⟩
  intro w
  obtain ⟨t, ht⟩ := LinearMap.lTensor_surjective (ComplexAt σ) (intEquiv φ).surjective (coordInv σ w)
  refine ⟨t, ?_⟩
  show coordMap r σ (((intEquiv φ).toLinearMap).lTensor (ComplexAt σ) t) = w
  rw [ht, coordMap_coordInv]
theorem fibreCoord_conjMap (σ : K →+* ℂ) (x : Fibre σ V) :
    fibreCoord φ (conjugate σ) (conjMap σ V x) = star (fibreCoord φ σ x) := by
  simp only [fibreCoord, LinearMap.comp_apply]
  rw [← conjMap_fibreMap, coordMap_conjMap]
def fibreCoordEquiv (σ : K →+* ℂ) : Fibre σ V ≃ₗ[ℂ] (Fin r → ℂ) :=
  LinearEquiv.ofBijective (fibreCoord φ σ) (fibreCoord_bijective φ σ)
theorem fibreCoordEquiv_symm_star (σ : K →+* ℂ) (w : Fin r → ℂ) :
    (fibreCoordEquiv φ (conjugate σ)).symm (star w) = conjMap σ V ((fibreCoordEquiv φ σ).symm w) := by
  rw [LinearEquiv.symm_apply_eq]
  change star w = fibreCoord φ (conjugate σ) (conjMap σ V _)
  rw [fibreCoord_conjMap]
  congr 1
  exact ((fibreCoordEquiv φ σ).apply_symm_apply w).symm
def normsOf (H : HermitianSpace K r) : HermitianNorms K V where
  form σ := coreComap (H.form σ) (fibreCoord φ σ) (fibreCoord_bijective φ σ).1
  form_conj σ x y := by
    rw [coreComap_inner, coreComap_inner, fibreCoord_conjMap, fibreCoord_conjMap, H.form_conj]
def spaceOf (Nm : HermitianNorms K V) : HermitianSpace K r where
  form σ := coreComap (Nm.form σ) (fibreCoordEquiv φ σ).symm.toLinearMap
    (fibreCoordEquiv φ σ).symm.injective
  form_conj σ x y := by
    rw [coreComap_inner, coreComap_inner]
    simp only [LinearEquiv.coe_coe]
    rw [fibreCoordEquiv_symm_star, fibreCoordEquiv_symm_star, Nm.form_conj]
def pullLattice (M : Submodule (𝓞 K) (Fin r → K)) (hM : IsLattice M) : FullLattice K V where
  carrier := M.map (intEquiv φ).symm.toLinearMap
  fg := hM.1.map _
  span_eq := by
    rw [Submodule.map_coe]
    change Submodule.span K (φ.symm.toLinearMap '' (M : Set (Fin r → K))) = ⊤
    rw [Submodule.span_image, hM.2, Submodule.map_top, LinearEquiv.range]
variable (v : HeightOneSpectrum (𝓞 K))
def localEquiv : (v.adicCompletion K ⊗[K] V) ≃ₗ[v.adicCompletion K] (Fin r → v.adicCompletion K) :=
  (LinearEquiv.baseChange K (v.adicCompletion K) V (Fin r → K) φ).trans
    (TensorProduct.piScalarRight K (v.adicCompletion K) (v.adicCompletion K) (Fin r))
def glEquiv (g : Matrix.GeneralLinearGroup (Fin r) (v.adicCompletion K)) :
    (Fin r → v.adicCompletion K) ≃ₗ[v.adicCompletion K] (Fin r → v.adicCompletion K) :=
  LinearEquiv.ofLinearMap (Matrix.toLin' (g : Matrix (Fin r) (Fin r) (v.adicCompletion K)))
    (Matrix.toLin' ((g⁻¹ : Matrix.GeneralLinearGroup (Fin r) (v.adicCompletion K)) :
      Matrix (Fin r) (Fin r) (v.adicCompletion K)))
    (by rw [← Matrix.toLin'_mul, Units.mul_inv, Matrix.toLin'_one])
    (by rw [← Matrix.toLin'_mul, Units.inv_mul, Matrix.toLin'_one])
def glOf (f : (Fin r → v.adicCompletion K) ≃ₗ[v.adicCompletion K] (Fin r → v.adicCompletion K)) :
    Matrix.GeneralLinearGroup (Fin r) (v.adicCompletion K) where
  val := LinearMap.toMatrix' (f : (Fin r → v.adicCompletion K) →ₗ[v.adicCompletion K] _)
  inv := LinearMap.toMatrix' (f.symm : (Fin r → v.adicCompletion K) →ₗ[v.adicCompletion K] _)
  val_inv := by
    rw [← LinearMap.toMatrix'_mul, ← LinearMap.toMatrix'_one]
    congr 1
    exact LinearMap.ext fun x ↦ f.apply_symm_apply x
  inv_val := by
    rw [← LinearMap.toMatrix'_mul, ← LinearMap.toMatrix'_one]
    congr 1
    exact LinearMap.ext fun x ↦ f.symm_apply_apply x
end LocalChangeEq
end
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.LatticeLemmas


