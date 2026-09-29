-- Prove2me | solution 1 for AutomorphicForm.measure_setOf_algebraNorm_det_sum_map_tmul_eq_zero_eq_zero_of_isUnit
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/a224b13b-6c30-5f1b-8bea-e690378e55ce

import Definitions.Def_AutomorphicForm_BaseChangePlaces
import Definitions.Def_AutomorphicForm_AdelicLsXi
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_AutomorphicForm_GodementSection
import Definitions.Def_AutomorphicForm_WhittakerCoefficient
import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_AutomorphicForm_TwistedCommutant

import Theorems.Thm_MvPolynomial_measure_setOf_eval_eq_zero_of_ne_zero
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_measure_setOf_algebraNorm_det_sum_map_tmul_eq_zero_eq_zero_of_isUnit

set_option autoImplicit false

open MeasureTheory Filter NumberField NumberField.AdelicHaar NumberField.AdelicFourier NumberField.AdelicBox NumberField.TateGlobal IsDedekindDomain AutomorphicForm

open scoped TensorProduct TensorProduct.RightActions ENNReal Topology SchwartzMap

attribute [local instance] NumberField.AdelicHaar.glBorel AutomorphicForm.centralizerBorel
  AutomorphicForm.twistedCentralizerBorel

open scoped Classical

open scoped Matrix

namespace Ws31
namespace NullDet

variable {K L A : Type} [Field K] [Field L] [Algebra K L] [Field A] [Algebra K A]

theorem smul_tmul_eq (a : A) (l : L) (a' : A) : a • (l ⊗ₜ[K] a') = l ⊗ₜ[K] (a * a') := rfl

theorem sum_map_tmul_eq_sum_smul {ι : Type} [Fintype ι] (b : ι → Matrix (Fin 2) (Fin 2) L) (a : ι → A) :
    (∑ i, (b i).map fun l : L => l ⊗ₜ[K] a i) = ∑ i, a i • (b i).map fun l : L => l ⊗ₜ[K] (1 : A) := by
  refine Finset.sum_congr rfl fun i _ => ?_
  ext r s
  simp only [Matrix.map_apply, Matrix.smul_apply, smul_tmul_eq, mul_one]

theorem norm_det_eq_det_toMatrix [Module.Finite K L] {κ : Type} [Fintype κ] [DecidableEq κ]
    (β : Module.Basis κ A (Fin 2 → L ⊗[K] A)) (M : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) :
    Algebra.norm A M.det = (LinearMap.toMatrix β β ((Matrix.toLin' M).restrictScalars A)).det := by
  rw [LinearMap.det_toMatrix, LinearMap.det_restrictScalars, LinearMap.det_toLin']

noncomputable def Tm {κ : Type} [Fintype κ] [DecidableEq κ]
    (β : Module.Basis κ A (Fin 2 → L ⊗[K] A)) (B : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) : Matrix κ κ A :=
  fun k l => β.repr (B *ᵥ β l) k

theorem toMatrix_eq_sum_smul {ι κ : Type} [Fintype ι] [Fintype κ] [DecidableEq κ]
    (β : Module.Basis κ A (Fin 2 → L ⊗[K] A)) (B : ι → Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) (a : ι → A) :
    LinearMap.toMatrix β β ((Matrix.toLin' (∑ i, a i • B i)).restrictScalars A) = ∑ i, a i • Tm β (B i) := by
  ext k l
  rw [LinearMap.toMatrix_apply, LinearMap.restrictScalars_apply, Matrix.toLin'_apply, Matrix.sum_mulVec,
    map_sum, Matrix.sum_apply, Finsupp.coe_finsetSum, Finset.sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.smul_mulVec, LinearEquiv.map_smul, Finsupp.coe_smul, Pi.smul_apply, Matrix.smul_apply, smul_eq_mul,
    smul_eq_mul]
  rfl

noncomputable def detPoly {ι κ : Type} [Fintype ι] [Fintype κ] [DecidableEq κ] (T : ι → Matrix κ κ A) :
    MvPolynomial ι A :=
  Matrix.det (∑ i, (MvPolynomial.X i : MvPolynomial ι A) • (T i).map (MvPolynomial.C : A →+* MvPolynomial ι A))

theorem eval_detPoly {ι κ : Type} [Fintype ι] [Fintype κ] [DecidableEq κ] (T : ι → Matrix κ κ A) (a : ι → A) :
    MvPolynomial.eval a (detPoly T) = Matrix.det (∑ i, a i • T i) := by
  unfold detPoly
  rw [RingHom.map_det, RingHom.mapMatrix_apply]
  congr 1
  ext k l
  simp only [Matrix.map_apply, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, map_sum, map_mul,
    MvPolynomial.eval_X, MvPolynomial.eval_C]

end Ws31.NullDet

open Ws31.NullDet in
theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (v : HeightOneSpectrum (𝓞 K))
    (ι : Type) [Fintype ι] [DecidableEq ι]
    (b : ι → Matrix (Fin 2) (Fin 2) L)
    (a₀ : ι → v.adicCompletion K)
    (h1 : IsUnit (Matrix.det (∑ i : ι, (b i).map fun l : L => l ⊗ₜ[K] a₀ i :
      Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K))))
    [MeasurableSpace (v.adicCompletion K)] [BorelSpace (v.adicCompletion K)]
    (μ : Measure (ι → v.adicCompletion K)) [μ.IsAddHaarMeasure] :
    μ {a : ι → v.adicCompletion K |
        Algebra.norm (v.adicCompletion K) (Matrix.det (∑ i : ι, (b i).map fun l : L => l ⊗ₜ[K] a i :
          Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K))) = 0} = 0 := by
  classical
  haveI : Module.Finite K L := Module.Finite.of_restrictScalars_finite ℚ K L
  set B : ι → Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K) :=
    fun i => (b i).map fun l : L => l ⊗ₜ[K] (1 : v.adicCompletion K) with hB
  have hmat : ∀ a : ι → v.adicCompletion K,
      (∑ i : ι, (b i).map fun l : L => l ⊗ₜ[K] a i : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) =
        ∑ i, a i • B i := fun a => sum_map_tmul_eq_sum_smul b a
  let β := Module.finBasis (v.adicCompletion K) (Fin 2 → L ⊗[K] v.adicCompletion K)
  have key : ∀ a : ι → v.adicCompletion K,
      Algebra.norm (v.adicCompletion K) (Matrix.det (∑ i : ι, (b i).map fun l : L => l ⊗ₜ[K] a i :
          Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K))) =
        MvPolynomial.eval a (detPoly fun i => Tm β (B i)) := by
    intro a
    rw [hmat, norm_det_eq_det_toMatrix β, toMatrix_eq_sum_smul β B a, eval_detPoly]
  have hP0 : (detPoly fun i => Tm β (B i)) ≠ 0 := by
    intro h0
    have h := key a₀
    rw [h0, map_zero] at h
    exact (h1.map (Algebra.norm (v.adicCompletion K))).ne_zero h
  have hF : ¬ DiscreteTopology (v.adicCompletion K) := by
    intro hd
    haveI := hd
    have hfin : Finite (v.adicCompletionIntegers K) := finite_of_compact_of_discrete
    haveI : CharZero (v.adicCompletion K) :=
      charZero_of_injective_algebraMap (algebraMap K (v.adicCompletion K)).injective
    have hinf : Infinite (v.adicCompletionIntegers K) := by
      refine Infinite.of_injective (fun n : ℕ => (n : v.adicCompletionIntegers K)) fun m n h => ?_
      have h' := congrArg (fun x : v.adicCompletionIntegers K => (x : v.adicCompletion K)) h
      simp only at h'
      push_cast at h'
      exact_mod_cast h'
    exact not_finite (v.adicCompletionIntegers K)
  have hset : {a : ι → v.adicCompletion K |
      Algebra.norm (v.adicCompletion K) (Matrix.det (∑ i : ι, (b i).map fun l : L => l ⊗ₜ[K] a i :
        Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K))) = 0} =
      {a : ι → v.adicCompletion K | MvPolynomial.eval a (detPoly fun i => Tm β (B i)) = 0} := by
    ext a
    simp only [Set.mem_setOf_eq, key]
  rw [hset]
  exact MvPolynomial.measure_setOf_eval_eq_zero_of_ne_zero (v.adicCompletion K) hF ι _ hP0 μ

#print axioms solution

end S_AutomorphicForm_measure_setOf_algebraNorm_det_sum_map_tmul_eq_zero_eq_zero_of_isUnit
end P2MW
export P2MW.S_AutomorphicForm_measure_setOf_algebraNorm_det_sum_map_tmul_eq_zero_eq_zero_of_isUnit (solution)
