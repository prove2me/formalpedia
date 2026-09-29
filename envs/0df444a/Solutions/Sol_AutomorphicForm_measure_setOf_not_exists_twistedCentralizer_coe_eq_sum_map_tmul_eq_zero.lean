-- Prove2me | solution 1 for AutomorphicForm.measure_setOf_not_exists_twistedCentralizer_coe_eq_sum_map_tmul_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/3e3c0300-94aa-5fd4-a7df-a6f4e04f90b7

import Mathlib
import Definitions.Def_AutomorphicForm_BaseChangePlaces
import Definitions.Def_AutomorphicForm_TwistedCommutant
import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_NumberField_AdelicBox
import Theorems.Thm_AutomorphicForm_exists_homeomorph_twistedCommutant_map_mul_scalar_forall_coe_eq_sum_map_tmul_of_linearIndependent
import Theorems.Thm_MvPolynomial_measure_setOf_eval_eq_zero_of_ne_zero
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_measure_setOf_not_exists_twistedCentralizer_coe_eq_sum_map_tmul_eq_zero

set_option autoImplicit false

open scoped TensorProduct

namespace PolyAux

section normUnit

variable {F R : Type*} [Field F] [CommRing R] [Algebra F R] [Module.Finite F R] [Module.Free F R]

theorem isUnit_iff_norm_ne_zero (r : R) : IsUnit r ↔ Algebra.norm F r ≠ 0 := by
  rw [Algebra.norm_apply, ← isUnit_iff_ne_zero, ← LinearMap.isUnit_iff_isUnit_det,
    Algebra.lmul_isUnit_iff]

end normUnit

section baseChange

variable {K : Type*} [Field K] {L : Type*} [Field L] [Algebra K L]
variable {S F : Type*} [CommRing S] [CommRing F] [Algebra K S] [Algebra K F] (φ : S →ₐ[K] F)
variable {κ : Type*} [Fintype κ] [DecidableEq κ] (bL : Module.Basis κ K L)

theorem basis_repr_map (y : S ⊗[K] L) (i : κ) :
    (Algebra.TensorProduct.basis F bL).repr (Algebra.TensorProduct.map φ (AlgHom.id K L) y) i
      = φ ((Algebra.TensorProduct.basis S bL).repr y i) := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul s l =>
      simp [Algebra.TensorProduct.basis_repr_tmul]
  | add y z hy hz => simp [map_add, hy, hz]

theorem leftMulMatrix_map (a : S ⊗[K] L) :
    Algebra.leftMulMatrix (Algebra.TensorProduct.basis F bL)
        (Algebra.TensorProduct.map φ (AlgHom.id K L) a)
      = (Algebra.leftMulMatrix (Algebra.TensorProduct.basis S bL) a).map φ := by
  ext i j
  rw [Matrix.map_apply, Algebra.leftMulMatrix_eq_repr_mul, Algebra.leftMulMatrix_eq_repr_mul,
    Algebra.TensorProduct.basis_apply, Algebra.TensorProduct.basis_apply,
    show ((1 : F) ⊗ₜ[K] bL j) = Algebra.TensorProduct.map φ (AlgHom.id K L) ((1 : S) ⊗ₜ[K] bL j) by
      simp,
    ← map_mul, basis_repr_map]

include bL in

theorem norm_map (a : S ⊗[K] L) :
    Algebra.norm F (Algebra.TensorProduct.map φ (AlgHom.id K L) a) = φ (Algebra.norm S a) := by
  rw [Algebra.norm_eq_matrix_det (Algebra.TensorProduct.basis F bL),
    Algebra.norm_eq_matrix_det (Algebra.TensorProduct.basis S bL), leftMulMatrix_map φ bL,
    AlgHom.map_det, AlgHom.mapMatrix_apply]

end baseChange

section main

variable (K F L : Type*) [Field K] [Field F] [Field L] [Algebra K F] [Algebra K L]
  [FiniteDimensional K L]
  (ι : Type*) [Fintype ι] (n : Type*) [Fintype n] [DecidableEq n] (b : ι → Matrix n n L)

noncomputable def genericMatrix : Matrix n n (MvPolynomial ι F ⊗[K] L) :=
  ∑ k, (b k).map fun l : L => (MvPolynomial.X k : MvPolynomial ι F) ⊗ₜ[K] l

noncomputable def normPoly : MvPolynomial ι F :=
  Algebra.norm (MvPolynomial ι F) (genericMatrix K F L ι n b).det

theorem comm_mapMatrix_eq (x : ι → F) :
    (Algebra.TensorProduct.comm K L F).mapMatrix (∑ k, (b k).map fun l : L => l ⊗ₜ[K] x k)
      = (Algebra.TensorProduct.map
          ((MvPolynomial.aeval x : MvPolynomial ι F →ₐ[F] F).restrictScalars K)
          (AlgHom.id K L)).mapMatrix (genericMatrix K F L ι n b) := by
  simp only [map_sum, AlgEquiv.mapMatrix_apply, AlgHom.mapMatrix_apply, Matrix.map_map,
    genericMatrix]
  refine Finset.sum_congr rfl fun k _ => ?_
  congr 1
  funext l
  simp

theorem eval_normPoly (x : ι → F) :
    MvPolynomial.eval x (normPoly K F L ι n b)
      = Algebra.norm F
          ((∑ k, (b k).map fun l : L => l ⊗ₜ[K] x k).map (Algebra.TensorProduct.comm K L F)).det := by
  classical
  have hφ : ∀ q : MvPolynomial ι F,
      ((MvPolynomial.aeval x : MvPolynomial ι F →ₐ[F] F).restrictScalars K) q
        = MvPolynomial.eval x q := fun q => rfl
  rw [normPoly, ← hφ, ← norm_map _ (Module.finBasis K L), AlgHom.map_det,
    ← comm_mapMatrix_eq, AlgEquiv.mapMatrix_apply]

theorem isUnit_iff_eval_normPoly_ne_zero (x : ι → F) :
    IsUnit (∑ k, (b k).map fun l : L => l ⊗ₜ[K] x k)
      ↔ MvPolynomial.eval x (normPoly K F L ι n b) ≠ 0 := by
  classical
  rw [← MulEquiv.isUnit_map (Algebra.TensorProduct.comm K L F).mapMatrix,
    Matrix.isUnit_iff_isUnit_det, isUnit_iff_norm_ne_zero (F := F), eval_normPoly,
    AlgEquiv.mapMatrix_apply]

theorem normPoly_ne_zero_of_eq_one (x₀ : ι → F)
    (h : (∑ k, (b k).map fun l : L => l ⊗ₜ[K] x₀ k) = 1) : normPoly K F L ι n b ≠ 0 := by
  intro hp
  have h1 := (isUnit_iff_eval_normPoly_ne_zero K F L ι n b x₀).mp (h ▸ isUnit_one)
  exact h1 (by rw [hp, map_zero])

end main

end PolyAux

theorem exists_mvPolynomial_forall_isUnit_sum_map_tmul_iff_eval_ne_zero
    (K F L : Type) [Field K] [Field F] [Field L] [Algebra K F] [Algebra K L] [FiniteDimensional K L]
    (ι : Type) [Fintype ι] (n : Type) [Fintype n] [DecidableEq n] (b : ι → Matrix n n L) :
    ∃ p : MvPolynomial ι F, ∀ x : ι → F,
      (IsUnit (∑ k, (b k).map fun l : L => l ⊗ₜ[K] x k) ↔ MvPolynomial.eval x p ≠ 0) :=
  ⟨PolyAux.normPoly K F L ι n b, PolyAux.isUnit_iff_eval_normPoly_ne_zero K F L ι n b⟩

namespace E8A
namespace LN

open MeasureTheory NumberField IsDedekindDomain
open scoped TensorProduct

theorem not_discreteTopology_adicCompletion (K : Type) [Field K] [NumberField K]
    (v : HeightOneSpectrum (𝓞 K)) : ¬ DiscreteTopology (v.adicCompletion K) := by
  intro hd
  have hc : IsCompact ((v.adicCompletionIntegers K : Set (v.adicCompletion K))) :=
    isCompact_iff_compactSpace.2 (NumberField.AdelicHaar.compactSpace_adicCompletionIntegers (𝓞 K) K v)
  have hfin : ((v.adicCompletionIntegers K : Set (v.adicCompletion K))).Finite := hc.finite_of_discrete
  have hinj : Function.Injective (fun r : 𝓞 K => algebraMap K (v.adicCompletion K) (algebraMap (𝓞 K) K r)) :=
    (algebraMap K (v.adicCompletion K)).injective.comp (IsFractionRing.injective (𝓞 K) K)
  have hinf : ((v.adicCompletionIntegers K : Set (v.adicCompletion K))).Infinite :=
    Set.infinite_of_injective_forall_mem hinj
      (fun r => NumberField.AdelicBox.algebraMap_mem_adicCompletionIntegers (𝓞 K) K v r)
  exact hinf hfin

theorem measure_setOf_not_exists_twistedCentralizer_coe_eq_sum_eq_zero
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (h2 : Module.finrank K L = 2) (σ : L ≃ₐ[K] L) (δ₀ : GL (Fin 2) L) (c : (L ⊗[K] AdeleRing (𝓞 K) K)ˣ)
    (w : HeightOneSpectrum (𝓞 K))
    (ι : Type) [Fintype ι] [DecidableEq ι] (b : ι → Matrix (Fin 2) (Fin 2) L) (hb : LinearIndependent K b)
    (hbspan : ∀ X : Matrix (Fin 2) (Fin 2) L,
      X * (δ₀ : Matrix (Fin 2) (Fin 2) L) = (δ₀ : Matrix (Fin 2) (Fin 2) L) * X.map σ ↔
        X ∈ Submodule.span K (Set.range b))
    [MeasurableSpace (w.adicCompletion K)] [BorelSpace (w.adicCompletion K)]
    (μ : Measure (ι → w.adicCompletion K)) [μ.IsAddHaarMeasure] :
    μ {a : ι → w.adicCompletion K | ¬ ∃ t : ↥(AutomorphicForm.twistedCentralizer K L (w.adicCompletion K) σ
          (AutomorphicForm.tensorPlace K L w (Matrix.GeneralLinearGroup.map
            (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ *
          Matrix.GeneralLinearGroup.scalar (Fin 2) c))),
          ((t : GL (Fin 2) (L ⊗[K] w.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] w.adicCompletion K)) =
            ∑ k, (b k).map fun l : L => l ⊗ₜ[K] a k} = 0 := by
  classical
  haveI : FiniteDimensional K L := Module.finite_of_finrank_eq_succ h2

  have h1 : (1 : Matrix (Fin 2) (Fin 2) L) ∈ Submodule.span K (Set.range b) :=
    (hbspan 1).mp (by rw [Matrix.map_one σ (map_zero σ) (map_one σ), one_mul, mul_one])
  obtain ⟨β, hβ⟩ := (Submodule.mem_span_range_iff_exists_fun K).mp h1
  have hA1 : (∑ k, (b k).map fun l : L => l ⊗ₜ[K] (algebraMap K (w.adicCompletion K) (β k))) = 1 := by
    have hre : (∑ k, (b k).map fun l : L => l ⊗ₜ[K] (algebraMap K (w.adicCompletion K) (β k))) =
        (∑ k, β k • b k).map (fun l : L => l ⊗ₜ[K] (1 : w.adicCompletion K)) := by
      ext i j
      simp only [Matrix.sum_apply, Matrix.map_apply, Matrix.smul_apply, TensorProduct.sum_tmul,
        Algebra.algebraMap_eq_smul_one, TensorProduct.tmul_smul, TensorProduct.smul_tmul]
    rw [hre, hβ, Matrix.map_one (fun l : L => l ⊗ₜ[K] (1 : w.adicCompletion K)) (TensorProduct.zero_tmul _ _) rfl]

  have hp0 : PolyAux.normPoly K (w.adicCompletion K) L ι (Fin 2) b ≠ 0 :=
    PolyAux.normPoly_ne_zero_of_eq_one K (w.adicCompletion K) L ι (Fin 2) b _ hA1

  set cw : (L ⊗[K] w.adicCompletion K)ˣ := Units.map (AutomorphicForm.tensorPlaceHom K L w).toRingHom.toMonoidHom c
    with hcw
  have hδ₁ : AutomorphicForm.tensorPlace K L w (Matrix.GeneralLinearGroup.map
        (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀) =
      Matrix.GeneralLinearGroup.map
        (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] w.adicCompletion K) δ₀ :=
    Matrix.GeneralLinearGroup.ext (fun i j => rfl)
  have hδ₂ : AutomorphicForm.tensorPlace K L w (Matrix.GeneralLinearGroup.scalar (Fin 2) c) =
      Matrix.GeneralLinearGroup.scalar (Fin 2) cw := by
    apply Units.ext
    change (Matrix.scalar (Fin 2) (c : L ⊗[K] AdeleRing (𝓞 K) K)).map
        (AutomorphicForm.tensorPlaceHom K L w).toRingHom =
      Matrix.scalar (Fin 2) ((cw : (L ⊗[K] w.adicCompletion K)ˣ) : L ⊗[K] w.adicCompletion K)
    rw [Matrix.scalar_apply, Matrix.scalar_apply, Matrix.diagonal_map (map_zero _)]
    rfl
  have hδ : AutomorphicForm.tensorPlace K L w (Matrix.GeneralLinearGroup.map
        (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ *
          Matrix.GeneralLinearGroup.scalar (Fin 2) c) =
      Matrix.GeneralLinearGroup.map
        (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] w.adicCompletion K) δ₀ *
          Matrix.GeneralLinearGroup.scalar (Fin 2) cw := by
    rw [map_mul, hδ₁, hδ₂]
  obtain ⟨e, he⟩ :=
    AutomorphicForm.exists_homeomorph_twistedCommutant_map_mul_scalar_forall_coe_eq_sum_map_tmul_of_linearIndependent
      K L (w.adicCompletion K) σ δ₀ cw ι b hb hbspan

  have hsub : {a : ι → w.adicCompletion K | ¬ ∃ t : ↥(AutomorphicForm.twistedCentralizer K L (w.adicCompletion K) σ
          (AutomorphicForm.tensorPlace K L w (Matrix.GeneralLinearGroup.map
            (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ *
          Matrix.GeneralLinearGroup.scalar (Fin 2) c))),
          ((t : GL (Fin 2) (L ⊗[K] w.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] w.adicCompletion K)) =
            ∑ k, (b k).map fun l : L => l ⊗ₜ[K] a k} ⊆
      {a : ι → w.adicCompletion K | MvPolynomial.eval a (PolyAux.normPoly K (w.adicCompletion K) L ι (Fin 2) b) = 0} := by
    intro a ha
    by_contra hne
    apply ha
    have hu : IsUnit (∑ k, (b k).map fun l : L => l ⊗ₜ[K] a k) :=
      (PolyAux.isUnit_iff_eval_normPoly_ne_zero K (w.adicCompletion K) L ι (Fin 2) b a).mpr hne
    refine ⟨⟨hu.unit, ?_⟩, hu.unit_spec⟩
    rw [hδ, AutomorphicForm.mem_twistedCentralizer_iff_coe_mem_twistedCommutant, hu.unit_spec, ← he a]
    exact (e a).2
  exact measure_mono_null hsub
    (MvPolynomial.measure_setOf_eval_eq_zero_of_ne_zero (w.adicCompletion K)
      (not_discreteTopology_adicCompletion K w) ι _ hp0 μ)

end E8A.LN

open MeasureTheory NumberField IsDedekindDomain AutomorphicForm
open scoped TensorProduct TensorProduct.RightActions

theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (h2 : Module.finrank K L = 2) (σ : L ≃ₐ[K] L) (δ₀ : GL (Fin 2) L) (c : (L ⊗[K] AdeleRing (𝓞 K) K)ˣ)
    (w : HeightOneSpectrum (𝓞 K))
    (ι : Type) [Fintype ι] [DecidableEq ι] (b : ι → Matrix (Fin 2) (Fin 2) L) (hb : LinearIndependent K b)
    (hbspan : ∀ X : Matrix (Fin 2) (Fin 2) L,
      X * (δ₀ : Matrix (Fin 2) (Fin 2) L) = (δ₀ : Matrix (Fin 2) (Fin 2) L) * X.map σ ↔
        X ∈ Submodule.span K (Set.range b))
    [MeasurableSpace (w.adicCompletion K)] [BorelSpace (w.adicCompletion K)]
    (μ : Measure (ι → w.adicCompletion K)) [μ.IsAddHaarMeasure] :
    μ {a : ι → w.adicCompletion K | ¬ ∃ t : ↥(AutomorphicForm.twistedCentralizer K L (w.adicCompletion K) σ
          (AutomorphicForm.tensorPlace K L w (Matrix.GeneralLinearGroup.map
            (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ *
          Matrix.GeneralLinearGroup.scalar (Fin 2) c))),
          ((t : GL (Fin 2) (L ⊗[K] w.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] w.adicCompletion K)) =
            ∑ k, (b k).map fun l : L => l ⊗ₜ[K] a k} = 0 :=
  E8A.LN.measure_setOf_not_exists_twistedCentralizer_coe_eq_sum_eq_zero K L h2 σ δ₀ c w ι b hb hbspan μ

end S_AutomorphicForm_measure_setOf_not_exists_twistedCentralizer_coe_eq_sum_map_tmul_eq_zero
end P2MW
export P2MW.S_AutomorphicForm_measure_setOf_not_exists_twistedCentralizer_coe_eq_sum_map_tmul_eq_zero (solution)
