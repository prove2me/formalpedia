-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_DualProjApply
-- name    : GroundTheory_HeightsAndTheta_Heights_HeightKernels_DualProjApply
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T01:01:43.631945+00:00
-- url     : https://prove2.me/theorems/cf6c7828-4fd2-4761-bd20-fc0492583a3f
-- title:
--   Dual Proj Apply
-- statement:
--   Definitions and structural lemmas for Dual Proj Apply, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/DualProjApply.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsLineDegreeDual
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights
open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial Matrix NumberField
noncomputable section
variable {K : Type} [Field K] [NumberField K] {i : ℕ} {F : HermLattice K i}
  {T : Type} [Fintype T] [DecidableEq T]
def dualProj (b : Module.Basis T ℤ (dualLattice F))
    (hb : Function.Bijective (Matrix.mulVecLin (dualEmbMatrix b))) :
    (((k : Unit) → dualBlocks T k) → ℂ) →ₗ[ℂ] (Fin i → ℂ) :=
  ∑ σ : K →+* ℂ, (LinearMap.pi fun j : Fin i => LinearMap.proj (σ, j)) ∘ₗ
    (dualRecover b hb).toLinearMap ∘ₗ (LinearMap.pi fun t : T => LinearMap.proj fun _ : Unit => t)
def dualPlanePt (b : Module.Basis T ℤ (dualLattice F)) (σ : K →+* ℂ) (v : Fin i → ℂ) :
    (Σ _ : Unit, T) → ℂ :=
  fun p => ∑ j, σ ((b p.2 : Fin i → K) j) * v j
def DualPtsOnPlane.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (i : ℕ) (F : HermLattice K i) (T : Type) [Fintype T]
    [DecidableEq T] (b : Module.Basis T ℤ (dualLattice F))
    (hb : Function.Bijective (Matrix.mulVecLin (dualEmbMatrix b))),
    ∀ z ∈ mcPts (dualIdeal b), ∃ σ : K →+* ℂ, ∀ τ : K →+* ℂ, τ ≠ σ → ∀ j,
      dualRecover b hb (fun t => z ⟨(), t⟩) (τ, j) = 0
def DualPtsOfPlane.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (i : ℕ) (F : HermLattice K i) (T : Type) [Fintype T]
    [DecidableEq T] (b : Module.Basis T ℤ (dualLattice F))
    (_hb : Function.Bijective (Matrix.mulVecLin (dualEmbMatrix b))) (σ : K →+* ℂ) (v : Fin i → ℂ),
    v ≠ 0 → dualPlanePt b σ v ∈ mcPts (dualIdeal b)
def DualStdMassAt.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (D : ℕ) (F : HermLattice K (D + 1)) (T : Type) [Fintype T]
    [DecidableEq T] (b : Module.Basis T ℤ (dualLattice F))
    (hb : Function.Bijective (Matrix.mulVecLin (dualEmbMatrix b))),
    (∀ σ, F.metric σ = 1) →
    ptsIntegralAt (e := D) (dualIdeal b) (dualProj b hb)
      (fun _ z => Real.log ((dualLine F b hb).h z)) (fun _ => 1) = Fintype.card (K →+* ℂ)
example : (((k : Unit) → dualBlocks Unit k) → ℂ) →ₗ[ℂ] (Fin 1 → ℂ) :=
  dualProj dualBasisStandard dualEmbMatrix_standard_bijective
example : (Σ _ : Unit, Unit) → ℂ := dualPlanePt dualBasisStandard (Rat.castHom ℂ) fun _ => 1
example : ∃ (b : Module.Basis Unit ℤ (dualLattice (HermLattice.standard ℚ 1)))
    (_ : Function.Bijective (Matrix.mulVecLin (dualEmbMatrix b))) (_ : ℚ →+* ℂ) (v : Fin 1 → ℂ), v ≠ 0 :=
  ⟨dualBasisStandard, dualEmbMatrix_standard_bijective, Rat.castHom ℂ, fun _ => 1,
    fun h => one_ne_zero (congrFun h 0)⟩
example : ∃ (b : Module.Basis Unit ℤ (dualLattice (HermLattice.standard ℚ (0 + 1))))
    (_ : Function.Bijective (Matrix.mulVecLin (dualEmbMatrix b))),
    ∀ σ, (HermLattice.standard ℚ (0 + 1)).metric σ = 1 :=
  ⟨dualBasisStandard, dualEmbMatrix_standard_bijective, fun _ => rfl⟩
end
end GroundTheory.Heights₂.Heights


