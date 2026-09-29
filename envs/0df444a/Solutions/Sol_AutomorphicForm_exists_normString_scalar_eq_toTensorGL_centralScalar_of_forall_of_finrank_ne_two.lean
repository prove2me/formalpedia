-- Prove2me | solution 1 for AutomorphicForm.exists_normString_scalar_eq_toTensorGL_centralScalar_of_forall_of_finrank_ne_two
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/5bf71cd6-1ec3-5900-baa9-62d7f497e0ac

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_AutomorphicForm_AdelicLsXi
import Theorems.Thm_AutomorphicForm_exists_normString_eq_toTensorGL_of_mem_localIntegralSet_of_ramificationIdx_eq_one_of_prime
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_normString_scalar_eq_toTensorGL_centralScalar_of_forall_of_finrank_ne_two

set_option autoImplicit false

open NumberField IsDedekindDomain
open scoped TensorProduct

noncomputable section

namespace AutomorphicForm
p2m_export "AutomorphicForm" "toTensorGL semiLocalIntegers sigmaTensor sigmaGL normString mem_integralUnitsSet localIntegralSet mem_localIntegralSet centralScalar exists_normString_eq_toTensorGL_of_mem_localIntegralSet_of_ramificationIdx_eq_one_of_prime"
namespace ScalarNormGluing
p2m_open "AutomorphicForm"

section NormAlgebra

variable {K L : Type} [Field K] [Field L] [Algebra K L]
variable {A : Type} [CommRing A] [Algebra K A] (σ : L ≃ₐ[K] L)

def sT : (L ⊗[K] A)ˣ →* (L ⊗[K] A)ˣ := Units.map (sigmaTensor K L A σ).toMonoidHom

def scalarNorm (z : (L ⊗[K] A)ˣ) : (L ⊗[K] A)ˣ :=
  ((List.range (Module.finrank K L)).map fun i => (⇑(sT (A := A) σ))^[i] z).prod

def ι : Aˣ →* (L ⊗[K] A)ˣ :=
  Units.map (Algebra.TensorProduct.includeRight : A →ₐ[K] L ⊗[K] A).toRingHom.toMonoidHom

theorem sigmaGL_scalar (z : (L ⊗[K] A)ˣ) :
    sigmaGL K L A σ (Matrix.GeneralLinearGroup.scalar (Fin 2) z) =
      Matrix.GeneralLinearGroup.scalar (Fin 2) (sT σ z) := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  show sigmaTensor K L A σ ((Matrix.GeneralLinearGroup.scalar (Fin 2) z : Matrix (Fin 2) (Fin 2) _) i j) = _
  simp only [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.diagonal_apply]
  split_ifs <;> simp [sT]

theorem iterate_sigmaGL_scalar (i : ℕ) (z : (L ⊗[K] A)ˣ) :
    (⇑(sigmaGL K L A σ))^[i] (Matrix.GeneralLinearGroup.scalar (Fin 2) z) =
      Matrix.GeneralLinearGroup.scalar (Fin 2) ((⇑(sT (A := A) σ))^[i] z) :=
  (Function.Semiconj.iterate_right (f := (Matrix.GeneralLinearGroup.scalar (Fin 2) : (L ⊗[K] A)ˣ → _))
    (ga := sT (A := A) σ) (gb := sigmaGL K L A σ) (fun x => (sigmaGL_scalar σ x).symm) i z).symm

theorem normString_scalar (z : (L ⊗[K] A)ˣ) :
    normString K L A σ (Matrix.GeneralLinearGroup.scalar (Fin 2) z) =
      Matrix.GeneralLinearGroup.scalar (Fin 2) (scalarNorm σ z) := by
  unfold normString scalarNorm
  rw [map_list_prod, List.map_map]
  congr 1
  refine List.map_congr_left fun i _ => ?_
  exact iterate_sigmaGL_scalar σ i z

theorem det_sigmaGL (g : GL (Fin 2) (L ⊗[K] A)) :
    Matrix.GeneralLinearGroup.det (sigmaGL K L A σ g) = sT σ (Matrix.GeneralLinearGroup.det g) := by
  refine Units.ext ?_
  show Matrix.det ((sigmaTensor K L A σ).mapMatrix (g : Matrix (Fin 2) (Fin 2) _)) =
    sigmaTensor K L A σ (Matrix.det _)
  rw [RingHom.map_det]

theorem det_normString (δ : GL (Fin 2) (L ⊗[K] A)) :
    Matrix.GeneralLinearGroup.det (normString K L A σ δ) =
      scalarNorm σ (Matrix.GeneralLinearGroup.det δ) := by
  unfold normString scalarNorm
  rw [map_list_prod, List.map_map]
  congr 1
  refine List.map_congr_left fun i _ => ?_
  exact Function.Semiconj.iterate_right
    (f := (Matrix.GeneralLinearGroup.det : GL (Fin 2) (L ⊗[K] A) → _))
    (ga := sigmaGL K L A σ) (gb := sT (A := A) σ) (fun x => det_sigmaGL σ x) i δ

theorem sT_ι (r : Aˣ) : sT σ (ι (K := K) (L := L) r) = ι r := by
  refine Units.ext ?_
  show sigmaTensor K L A σ ((1 : L) ⊗ₜ (r : A)) = (1 : L) ⊗ₜ (r : A)
  simp [sigmaTensor]

theorem scalarNorm_ι (r : Aˣ) :
    scalarNorm σ (ι (K := K) (L := L) r) = ι r ^ Module.finrank K L := by
  unfold scalarNorm
  have : ((List.range (Module.finrank K L)).map fun i =>
      (⇑(sT (A := A) σ))^[i] (ι (K := K) (L := L) r)) =
      (List.range (Module.finrank K L)).map fun _ => ι (K := K) (L := L) r := by
    refine List.map_congr_left fun i _ => ?_
    exact Function.iterate_fixed (sT_ι σ r) i
  rw [this, List.map_const', List.prod_replicate, List.length_range]

theorem toTensorGL_scalar (r : Aˣ) :
    toTensorGL K L A (Matrix.GeneralLinearGroup.scalar (Fin 2) r) =
      Matrix.GeneralLinearGroup.scalar (Fin 2) (ι (K := K) (L := L) r) := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  show (Algebra.TensorProduct.includeRight : A →ₐ[K] L ⊗[K] A)
      ((Matrix.GeneralLinearGroup.scalar (Fin 2) r : Matrix (Fin 2) (Fin 2) A) i j) = _
  simp only [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.diagonal_apply]
  split_ifs <;> simp [ι]

theorem det_toTensorGL (g : GL (Fin 2) A) :
    Matrix.GeneralLinearGroup.det (toTensorGL K L A g) =
      ι (K := K) (L := L) (Matrix.GeneralLinearGroup.det g) := by
  refine Units.ext ?_
  show Matrix.det ((Algebra.TensorProduct.includeRight : A →ₐ[K] L ⊗[K] A).toRingHom.mapMatrix
      (g : Matrix (Fin 2) (Fin 2) A)) =
    (Algebra.TensorProduct.includeRight : A →ₐ[K] L ⊗[K] A).toRingHom
      (Matrix.det (g : Matrix (Fin 2) (Fin 2) A))
  rw [RingHom.map_det]

theorem normString_scalar_ι (r : Aˣ) :
    normString K L A σ (Matrix.GeneralLinearGroup.scalar (Fin 2) (ι (K := K) (L := L) r)) =
      toTensorGL K L A (Matrix.GeneralLinearGroup.scalar (Fin 2) (r ^ Module.finrank K L)) := by
  rw [normString_scalar, scalarNorm_ι, ← map_pow, toTensorGL_scalar]

end NormAlgebra

section GLScalar

variable {R S : Type*} [CommRing R] [CommRing S]

theorem glmap_scalar (f : R →+* S) (r : Rˣ) :
    Matrix.GeneralLinearGroup.map (n := Fin 2) f (Matrix.GeneralLinearGroup.scalar (Fin 2) r) =
      Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.map (f : R →* S) r) := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  rw [Matrix.GeneralLinearGroup.map_apply]
  simp only [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.diagonal_apply, Units.coe_map,
    MonoidHom.coe_coe]
  split_ifs <;> simp

end GLScalar

section Arch

theorem real_exists_pow_eq_of_odd {n : ℕ} (hn : Odd n) (x : ℝ) : ∃ y : ℝ, y ^ n = x := by
  have hn0 : n ≠ 0 := by obtain ⟨k, rfl⟩ := hn; omega
  rcases le_or_gt 0 x with hx | hx
  · exact ⟨x ^ (n⁻¹ : ℝ), Real.rpow_inv_natCast_pow hx hn0⟩
  · refine ⟨-((-x) ^ (n⁻¹ : ℝ)), ?_⟩
    rw [hn.neg_pow, Real.rpow_inv_natCast_pow (neg_nonneg.2 hx.le) hn0, neg_neg]

variable (K : Type) [Field K]

theorem completion_exists_pow_eq_of_odd (w : InfinitePlace K) {n : ℕ} (hn : Odd n) (hn0 : n ≠ 0)
    (x : w.Completion) : ∃ y : w.Completion, y ^ n = x := by
  rcases w.isReal_or_isComplex with hw | hw
  · let e := NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal hw
    obtain ⟨y, hy⟩ := real_exists_pow_eq_of_odd hn (e x)
    refine ⟨e.symm y, e.injective ?_⟩
    rw [map_pow, RingEquiv.apply_symm_apply, hy]
  · let e := NumberField.InfinitePlace.Completion.ringEquivComplexOfIsComplex hw
    obtain ⟨y, hy⟩ := IsAlgClosed.exists_pow_nat_eq (e x) (Nat.pos_of_ne_zero hn0)
    refine ⟨e.symm y, e.injective ?_⟩
    rw [map_pow, RingEquiv.apply_symm_apply, hy]

theorem infiniteAdeleRing_exists_pow_eq_of_odd {n : ℕ} (hn : Odd n) (hn0 : n ≠ 0)
    (x : InfiniteAdeleRing K) : ∃ y : InfiniteAdeleRing K, y ^ n = x := by
  have h := fun w : InfinitePlace K => completion_exists_pow_eq_of_odd K w hn hn0 (x w)
  choose y hy using h
  exact ⟨y, funext fun w => hy w⟩

theorem infiniteAdeleRing_exists_units_pow_eq_of_odd {n : ℕ} (hn : Odd n) (hn0 : n ≠ 0)
    (x : (InfiniteAdeleRing K)ˣ) : ∃ y : (InfiniteAdeleRing K)ˣ, y ^ n = x := by
  obtain ⟨y, hy⟩ := infiniteAdeleRing_exists_pow_eq_of_odd K hn hn0 (x : InfiniteAdeleRing K)
  have hyu : IsUnit y := (isUnit_pow_iff hn0).1 (by rw [hy]; exact x.isUnit)
  refine ⟨hyu.unit, Units.ext ?_⟩
  rw [Units.val_pow_eq_pow_val, IsUnit.unit_spec, hy]

variable (L : Type) [Field L] [Algebra K L] [NumberField K] (σ : L ≃ₐ[K] L)

theorem exists_arch (hodd : Odd (Module.finrank K L)) (hne : Module.finrank K L ≠ 0)
    (u : (AdeleRing (𝓞 K) K)ˣ) :
    ∃ za : (L ⊗[K] InfiniteAdeleRing K)ˣ,
      normString K L (InfiniteAdeleRing K) σ (Matrix.GeneralLinearGroup.scalar (Fin 2) za) =
        toTensorGL K L (InfiniteAdeleRing K)
          (AdelicLevel.glArch (𝓞 K) K (centralScalar (𝓞 K) K u)) := by
  have hsc : AdelicLevel.glArch (𝓞 K) K (centralScalar (𝓞 K) K u) =
      Matrix.GeneralLinearGroup.scalar (Fin 2)
        (Units.map (AdelicLevel.adeleArch (𝓞 K) K : AdeleRing (𝓞 K) K →* InfiniteAdeleRing K) u) :=
    glmap_scalar _ _
  obtain ⟨y, hy⟩ := infiniteAdeleRing_exists_units_pow_eq_of_odd K hodd hne
    (Units.map (AdelicLevel.adeleArch (𝓞 K) K : AdeleRing (𝓞 K) K →* InfiniteAdeleRing K) u)
  refine ⟨ι (K := K) (L := L) y, ?_⟩
  rw [normString_scalar_ι, hy, hsc]

end Arch

section Local

def gam {R : Type*} [CommRing R] (a : Rˣ) (t : R) : GL (Fin 2) R where
  val := !![0, -(a : R); 1, t]
  inv := !![t * ((a⁻¹ : Rˣ) : R), 1; -((a⁻¹ : Rˣ) : R), 0]
  val_inv := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  inv_val := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, mul_assoc]

theorem det_gam {R : Type*} [CommRing R] (a : Rˣ) (t : R) :
    Matrix.GeneralLinearGroup.det (gam a t) = a := by
  refine Units.ext ?_
  show Matrix.det !![0, -(a : R); 1, t] = a
  simp [Matrix.det_fin_two]

theorem trace_gam {R : Type*} [CommRing R] (a : Rˣ) (t : R) :
    Matrix.trace (gam a t : Matrix (Fin 2) (Fin 2) R) = t := by
  show Matrix.trace !![0, -(a : R); 1, t] = t
  simp [Matrix.trace_fin_two]

theorem val_det_gam {R : Type*} [CommRing R] (a : Rˣ) (t : R) :
    Matrix.det (gam a t : Matrix (Fin 2) (Fin 2) R) = a := by
  show Matrix.det !![0, -(a : R); 1, t] = a
  simp [Matrix.det_fin_two]

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

theorem exists_trace_unit_discr (v : HeightOneSpectrum (𝓞 K)) (a : v.adicCompletion K)
    (ha : Valued.v a = 1) :
    ∃ t : v.adicCompletion K, t ∈ v.adicCompletionIntegers K ∧ Valued.v (t ^ 2 - 4 * a) = 1 := by
  by_cases h4 : Valued.v (4 : v.adicCompletion K) = 1
  · refine ⟨0, zero_mem _, ?_⟩
    rw [zero_pow two_ne_zero, zero_sub, Valuation.map_neg, map_mul, h4, ha, one_mul]
  · have h4mem : (4 : v.adicCompletion K) ∈ v.adicCompletionIntegers K := by
      simp
    have h4lt : Valued.v (4 * a) < 1 := by
      rw [map_mul, ha, mul_one]
      exact lt_of_le_of_ne h4mem h4
    refine ⟨1, one_mem _, ?_⟩
    rw [one_pow]
    exact Valuation.map_one_sub_of_lt _ h4lt

theorem gam_mem_localIntegralSet (v : HeightOneSpectrum (𝓞 K)) (a : (v.adicCompletion K)ˣ)
    (ha : (a : v.adicCompletion K) ∈ v.adicCompletionIntegers K)
    (ha' : ((a⁻¹ : (v.adicCompletion K)ˣ) : v.adicCompletion K) ∈ v.adicCompletionIntegers K)
    (t : v.adicCompletion K) (ht : t ∈ v.adicCompletionIntegers K) :
    gam a t ∈ localIntegralSet K v := by
  refine (mem_localIntegralSet K v).2 ⟨fun i j => ?_, fun i j => ?_⟩
  · change (!![0, -(a : v.adicCompletion K); 1, t] : Matrix (Fin 2) (Fin 2) _) i j ∈ _
    fin_cases i <;> fin_cases j
    · simp
    · simpa using neg_mem ha
    · simp
    · simpa using ht
  · change (!![t * ((a⁻¹ : (v.adicCompletion K)ˣ) : v.adicCompletion K), 1;
        -((a⁻¹ : (v.adicCompletion K)ˣ) : v.adicCompletion K), 0] : Matrix (Fin 2) (Fin 2) _) i j ∈ _
    fin_cases i <;> fin_cases j
    · simpa using mul_mem ht ha'
    · simp
    · simpa using neg_mem ha'
    · simp

omit [NumberField L] in

theorem det_mem_semiLocalIntegers (v : HeightOneSpectrum (𝓞 K))
    {M : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)}
    (hM : ∀ i j, M i j ∈ semiLocalIntegers K L v) : M.det ∈ semiLocalIntegers K L v := by
  have hS : ∀ i j, M i j ∈ (HeightOneSpectrum.tensorAdicCompletionIntegersTo K L (𝓞 L) v).range :=
    fun i j => (AlgHom.mem_range _).2 (hM i j)
  rw [Matrix.det_fin_two]
  exact (AlgHom.mem_range _).1 (sub_mem (mul_mem (hS 0 0) (hS 1 1)) (mul_mem (hS 0 1) (hS 1 0)))

theorem exists_units_normString_scalar_of_unramified
    (hdeg : (Module.finrank K L).Prime) (σ : L ≃ₐ[K] L) (hσ : σ ≠ 1)
    (v : HeightOneSpectrum (𝓞 K))
    (hv : ∀ w : HeightOneSpectrum (𝓞 L), HeightOneSpectrum.under (𝓞 K) w = v →
      Ideal.ramificationIdx' (HeightOneSpectrum.under (𝓞 K) w).asIdeal w.asIdeal = 1)
    (a : (v.adicCompletion K)ˣ)
    (ha : (a : v.adicCompletion K) ∈ v.adicCompletionIntegers K)
    (ha' : ((a⁻¹ : (v.adicCompletion K)ˣ) : v.adicCompletion K) ∈ v.adicCompletionIntegers K) :
    ∃ z : (L ⊗[K] v.adicCompletion K)ˣ,
      (z : L ⊗[K] v.adicCompletion K) ∈ semiLocalIntegers K L v ∧
      ((z⁻¹ : (L ⊗[K] v.adicCompletion K)ˣ) : L ⊗[K] v.adicCompletion K) ∈ semiLocalIntegers K L v ∧
      normString K L (v.adicCompletion K) σ (Matrix.GeneralLinearGroup.scalar (Fin 2) z) =
        toTensorGL K L (v.adicCompletion K) (Matrix.GeneralLinearGroup.scalar (Fin 2) a) := by

  have hva : Valued.v (a : v.adicCompletion K) = 1 := by
    refine le_antisymm ha ?_
    have hprod : Valued.v (a : v.adicCompletion K) *
        Valued.v ((a⁻¹ : (v.adicCompletion K)ˣ) : v.adicCompletion K) = 1 := by
      rw [← map_mul, Units.mul_inv, map_one]
    calc (1 : WithZero (Multiplicative ℤ))
        = Valued.v (a : v.adicCompletion K) *
            Valued.v ((a⁻¹ : (v.adicCompletion K)ˣ) : v.adicCompletion K) := hprod.symm
      _ ≤ Valued.v (a : v.adicCompletion K) * 1 := by gcongr; exact ha'
      _ = Valued.v (a : v.adicCompletion K) := mul_one _

  obtain ⟨t, ht, hdisc⟩ := exists_trace_unit_discr K v a hva
  have hγ : gam a t ∈ localIntegralSet K v := gam_mem_localIntegralSet K v a ha ha' t ht
  have hdisc' : Valued.v (Matrix.trace (gam a t : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) ^ 2 -
      4 * Matrix.det (gam a t : Matrix (Fin 2) (Fin 2) (v.adicCompletion K))) = 1 := by
    rw [trace_gam, val_det_gam]; exact hdisc

  obtain ⟨δ, hδ, hN⟩ :=
    AutomorphicForm.exists_normString_eq_toTensorGL_of_mem_localIntegralSet_of_ramificationIdx_eq_one_of_prime
      K L hdeg σ hσ v hv (gam a t) hγ hdisc'

  refine ⟨Matrix.GeneralLinearGroup.det δ, ?_, ?_, ?_⟩
  · exact det_mem_semiLocalIntegers K L v (mem_integralUnitsSet.1 hδ).1
  · rw [← map_inv]
    exact det_mem_semiLocalIntegers K L v (mem_integralUnitsSet.1 hδ).2
  · rw [normString_scalar, ← det_normString, hN, det_toTensorGL, det_gam, toTensorGL_scalar]

end Local

section General

variable (K L : Type) [Field K] [NumberField K] [Field L] [Algebra K L]

def piFin (v : HeightOneSpectrum (𝓞 K)) : AdeleRing (𝓞 K) K →ₐ[K] v.adicCompletion K :=
  { (AdelicLevel.finAdeleEval (𝓞 K) K v).comp (AdelicLevel.adeleFin (𝓞 K) K) with
    commutes' := fun _ => rfl }

def piArch : AdeleRing (𝓞 K) K →ₐ[K] InfiniteAdeleRing K :=
  { AdelicLevel.adeleArch (𝓞 K) K with commutes' := fun _ => rfl }

@[scoped simp] theorem piFin_apply (v : HeightOneSpectrum (𝓞 K)) (a : AdeleRing (𝓞 K) K) :
    piFin K v a = a.2 v := rfl

@[scoped simp] theorem piArch_apply (a : AdeleRing (𝓞 K) K) : piArch K a = a.1 := rfl

def compFin (v : HeightOneSpectrum (𝓞 K)) :
    L ⊗[K] AdeleRing (𝓞 K) K →ₐ[K] L ⊗[K] v.adicCompletion K :=
  Algebra.TensorProduct.map (AlgHom.id K L) (piFin K v)

def compArch : L ⊗[K] AdeleRing (𝓞 K) K →ₐ[K] L ⊗[K] InfiniteAdeleRing K :=
  Algebra.TensorProduct.map (AlgHom.id K L) (piArch K)

@[scoped simp] theorem compFin_tmul (v : HeightOneSpectrum (𝓞 K)) (l : L) (a : AdeleRing (𝓞 K) K) :
    compFin K L v (l ⊗ₜ a) = l ⊗ₜ (a.2 v) := rfl

@[scoped simp] theorem compArch_tmul (l : L) (a : AdeleRing (𝓞 K) K) :
    compArch K L (l ⊗ₜ a) = l ⊗ₜ a.1 := rfl

theorem compFin_sigmaTensor (σ : L ≃ₐ[K] L) (v : HeightOneSpectrum (𝓞 K))
    (z : L ⊗[K] AdeleRing (𝓞 K) K) :
    compFin K L v (sigmaTensor K L (AdeleRing (𝓞 K) K) σ z) =
      sigmaTensor K L (v.adicCompletion K) σ (compFin K L v z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp [hx, hy]
  | tmul l a => rfl

theorem compArch_sigmaTensor (σ : L ≃ₐ[K] L) (z : L ⊗[K] AdeleRing (𝓞 K) K) :
    compArch K L (sigmaTensor K L (AdeleRing (𝓞 K) K) σ z) =
      sigmaTensor K L (InfiniteAdeleRing K) σ (compArch K L z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp [hx, hy]
  | tmul l a => rfl

section GLmaps

variable {R S : Type} [CommRing R] [CommRing S]

theorem glmap_iterate_comm {f : R →+* S} {τR : R →+* R} {τS : S →+* S}
    (h : ∀ x, f (τR x) = τS (f x)) (n : ℕ) (g : GL (Fin 2) R) :
    Matrix.GeneralLinearGroup.map f ((⇑(Matrix.GeneralLinearGroup.map τR))^[n] g) =
      (⇑(Matrix.GeneralLinearGroup.map τS))^[n] (Matrix.GeneralLinearGroup.map f g) := by
  induction n generalizing g with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply, ih]
    congr 1
    ext i j
    simp [Matrix.GeneralLinearGroup.map_apply, h]

end GLmaps

variable (σ : L ≃ₐ[K] L)

theorem glmap_compFin_toTensorGL (v : HeightOneSpectrum (𝓞 K)) (γ : GL (Fin 2) (AdeleRing (𝓞 K) K)) :
    Matrix.GeneralLinearGroup.map (compFin K L v).toRingHom (toTensorGL K L (AdeleRing (𝓞 K) K) γ) =
      toTensorGL K L (v.adicCompletion K)
        (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K γ)) := by
  ext i j
  rfl

theorem glmap_compArch_toTensorGL (γ : GL (Fin 2) (AdeleRing (𝓞 K) K)) :
    Matrix.GeneralLinearGroup.map (compArch K L).toRingHom (toTensorGL K L (AdeleRing (𝓞 K) K) γ) =
      toTensorGL K L (InfiniteAdeleRing K) (AdelicLevel.glArch (𝓞 K) K γ) := by
  ext i j
  rfl

theorem glmap_compFin_normString (v : HeightOneSpectrum (𝓞 K)) (δ : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K)) :
    Matrix.GeneralLinearGroup.map (compFin K L v).toRingHom (normString K L (AdeleRing (𝓞 K) K) σ δ) =
      normString K L (v.adicCompletion K) σ
        (Matrix.GeneralLinearGroup.map (compFin K L v).toRingHom δ) := by
  simp only [normString, map_list_prod, List.map_map]
  congr 1
  apply List.map_congr_left
  intro i _
  simp only [Function.comp_apply, sigmaGL]
  exact glmap_iterate_comm (fun x => compFin_sigmaTensor K L σ v x) i δ

theorem glmap_compArch_normString (δ : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K)) :
    Matrix.GeneralLinearGroup.map (compArch K L).toRingHom (normString K L (AdeleRing (𝓞 K) K) σ δ) =
      normString K L (InfiniteAdeleRing K) σ
        (Matrix.GeneralLinearGroup.map (compArch K L).toRingHom δ) := by
  simp only [normString, map_list_prod, List.map_map]
  congr 1
  apply List.map_congr_left
  intro i _
  simp only [Function.comp_apply, sigmaGL]
  exact glmap_iterate_comm (fun x => compArch_sigmaTensor K L σ x) i δ

end General

section Coordinates

variable (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]

section Coord

variable (M : Type) [CommRing M] [Algebra K M]

abbrev bL : Module.Basis (Fin (Module.finrank K L)) K L := Module.finBasis K L

def coord (z : L ⊗[K] M) : Fin (Module.finrank K L) → M :=
  fun i => ((bL K L).baseChange M).repr (Algebra.TensorProduct.comm K L M z) i

theorem coord_add (z z' : L ⊗[K] M) : coord K L M (z + z') = coord K L M z + coord K L M z' := by
  funext i; simp [coord]

theorem coord_zero : coord K L M 0 = 0 := by
  funext i; simp [coord]

theorem sum_tmul_coord (z : L ⊗[K] M) :
    ∑ i, (bL K L i) ⊗ₜ[K] (coord K L M z i) = z := by
  apply (Algebra.TensorProduct.comm K L M).injective
  rw [map_sum]
  have h := ((bL K L).baseChange M).sum_repr (Algebra.TensorProduct.comm K L M z)
  rw [← h]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Algebra.TensorProduct.comm_tmul, coord, Module.Basis.baseChange_apply]
  rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]

theorem coord_sum_tmul (c : Fin (Module.finrank K L) → M) :
    coord K L M (∑ i, (bL K L i) ⊗ₜ[K] c i) = c := by
  funext j
  simp only [coord, map_sum, Algebra.TensorProduct.comm_tmul]
  have : ∀ i, (c i) ⊗ₜ[K] (bL K L i) = (c i) • ((bL K L).baseChange M i) := fun i => by
    rw [Module.Basis.baseChange_apply, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  simp_rw [this]
  simp [Finsupp.single_apply]

theorem coord_tmul (l : L) (m : M) (i : Fin (Module.finrank K L)) :
    coord K L M (l ⊗ₜ m) i = algebraMap K M ((bL K L).repr l i) * m := by
  have hl : l = ∑ j, (bL K L).repr l j • bL K L j := ((bL K L).sum_repr l).symm
  have : l ⊗ₜ[K] m = ∑ j, (bL K L j) ⊗ₜ[K] (algebraMap K M ((bL K L).repr l j) * m) := by
    conv_lhs => rw [hl]
    rw [TensorProduct.sum_tmul]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [TensorProduct.smul_tmul, Algebra.smul_def]
  rw [this, coord_sum_tmul]

variable {M} {N : Type} [CommRing N] [Algebra K N]

theorem coord_map (f : M →ₐ[K] N) (z : L ⊗[K] M) (i : Fin (Module.finrank K L)) :
    coord K L N (Algebra.TensorProduct.map (AlgHom.id K L) f z) i = f (coord K L M z i) := by
  conv_lhs => rw [← sum_tmul_coord K L M z]
  rw [map_sum]
  simp only [Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
  rw [coord_sum_tmul]

theorem eq_of_coord_eq {z z' : L ⊗[K] M} (h : coord K L M z = coord K L M z') : z = z' := by
  rw [← sum_tmul_coord K L M z, ← sum_tmul_coord K L M z', h]

end Coord

end Coordinates

section Adelic

variable (K L : Type) [Field K] [NumberField K] [Field L] [Algebra K L] [FiniteDimensional K L]

theorem eq_of_comp_eq {z z' : L ⊗[K] AdeleRing (𝓞 K) K} (ha : compArch K L z = compArch K L z')
    (hf : ∀ v, compFin K L v z = compFin K L v z') : z = z' := by
  apply eq_of_coord_eq K L (M := AdeleRing (𝓞 K) K)
  funext i
  refine Prod.ext ?_ ?_
  · have := congrArg (fun t => coord K L (InfiniteAdeleRing K) t i) ha
    simpa only [compArch, coord_map, piArch_apply] using this
  · refine FiniteAdeleRing.ext K fun v => ?_
    have := congrArg (fun t => coord K L (v.adicCompletion K) t i) (hf v)
    simpa only [compFin, coord_map, piFin_apply] using this

theorem exists_comp_eq (xa : L ⊗[K] InfiniteAdeleRing K)
    (xf : ∀ v : HeightOneSpectrum (𝓞 K), L ⊗[K] v.adicCompletion K)
    (hint : ∀ i, ∀ᶠ v in Filter.cofinite,
      coord K L (v.adicCompletion K) (xf v) i ∈ v.adicCompletionIntegers K) :
    ∃ z : L ⊗[K] AdeleRing (𝓞 K) K, compArch K L z = xa ∧ ∀ v, compFin K L v z = xf v := by
  let af : Fin (Module.finrank K L) → FiniteAdeleRing (𝓞 K) K :=
    fun i => ⟨fun v => coord K L (v.adicCompletion K) (xf v) i, hint i⟩
  let a : Fin (Module.finrank K L) → AdeleRing (𝓞 K) K :=
    fun i => (coord K L (InfiniteAdeleRing K) xa i, af i)
  refine ⟨∑ i, (bL K L i) ⊗ₜ[K] a i, ?_, fun v => ?_⟩
  · rw [map_sum]
    simp only [compArch_tmul]
    exact sum_tmul_coord K L (InfiniteAdeleRing K) xa
  · rw [map_sum]
    simp only [compFin_tmul]
    exact sum_tmul_coord K L (v.adicCompletion K) (xf v)

variable [NumberField L]

theorem eventually_coord_mem_of_mem_semiLocalIntegers :
    ∀ᶠ v : HeightOneSpectrum (𝓞 K) in Filter.cofinite,
      ∀ x ∈ semiLocalIntegers K L v, ∀ i,
        coord K L (v.adicCompletion K) x i ∈ v.adicCompletionIntegers K := by
  classical
  obtain ⟨s, hs⟩ := Module.finite_def.mp (inferInstance : Module.Finite (𝓞 K) (𝓞 L))

  have hgen : ∀ᶠ v : HeightOneSpectrum (𝓞 K) in Filter.cofinite, ∀ g ∈ s, ∀ i,
      algebraMap K (v.adicCompletion K) ((bL K L).repr (algebraMap (𝓞 L) L g) i) ∈
        v.adicCompletionIntegers K := by
    rw [Filter.eventually_all_finset]
    intro g _
    rw [Filter.eventually_all]
    intro i
    exact (algebraMap K (FiniteAdeleRing (𝓞 K) K) ((bL K L).repr (algebraMap (𝓞 L) L g) i)).2
  filter_upwards [hgen] with v hv

  have hOL : ∀ y : 𝓞 L, ∀ i,
      algebraMap K (v.adicCompletion K) ((bL K L).repr (algebraMap (𝓞 L) L y) i) ∈
        v.adicCompletionIntegers K := by
    intro y
    have hy : y ∈ Submodule.span (𝓞 K) (s : Set (𝓞 L)) := by rw [hs]; trivial
    refine Submodule.span_induction
      (p := fun (y : 𝓞 L) (_ : y ∈ Submodule.span (𝓞 K) (s : Set (𝓞 L))) => ∀ i,
        algebraMap K (v.adicCompletion K) ((bL K L).repr (algebraMap (𝓞 L) L y) i) ∈
          v.adicCompletionIntegers K)
      ?_ ?_ ?_ ?_ hy
    · intro g hg i
      exact hv g hg i
    · intro i
      rw [map_zero, map_zero, Finsupp.zero_apply, map_zero]
      exact zero_mem _
    · intro y z _ _ hy hz i
      rw [map_add, map_add, Finsupp.add_apply, map_add]
      exact add_mem (hy i) (hz i)
    · intro c y _ hy i
      have : algebraMap (𝓞 L) L (c • y) = (c : K) • algebraMap (𝓞 L) L y := by
        rw [Algebra.smul_def, Algebra.smul_def, map_mul]
        congr 1
      rw [this, map_smul, Finsupp.smul_apply, smul_eq_mul, map_mul]
      exact mul_mem (HeightOneSpectrum.coe_mem_adicCompletionIntegers v c) (hy i)

  rintro x ⟨t, rfl⟩
  induction t using TensorProduct.induction_on with
  | zero => intro i; simp [coord_zero]
  | add t₁ t₂ h₁ h₂ =>
    intro i
    rw [map_add, coord_add, Pi.add_apply]
    exact add_mem (h₁ i) (h₂ i)
  | tmul y o =>
    intro i
    rw [HeightOneSpectrum.tensorAdicCompletionIntegersTo_tmul, coord_tmul]
    exact mul_mem (hOL y i) o.2

omit [NumberField L] in

theorem gl_eq_of_comp_eq {g h : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K)}
    (ha : Matrix.GeneralLinearGroup.map (compArch K L).toRingHom g =
      Matrix.GeneralLinearGroup.map (compArch K L).toRingHom h)
    (hf : ∀ v, Matrix.GeneralLinearGroup.map (compFin K L v).toRingHom g =
      Matrix.GeneralLinearGroup.map (compFin K L v).toRingHom h) : g = h := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  apply eq_of_comp_eq K L
  · have := congrArg (fun t : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K) =>
      (t : Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) i j) ha
    simpa only [Matrix.GeneralLinearGroup.map_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe] using this
  · intro v
    have := congrArg (fun t : GL (Fin 2) (L ⊗[K] v.adicCompletion K) =>
      (t : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) i j) (hf v)
    simpa only [Matrix.GeneralLinearGroup.map_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe] using this

theorem units_exists_comp_eq (za : (L ⊗[K] InfiniteAdeleRing K)ˣ)
    (zf : ∀ v : HeightOneSpectrum (𝓞 K), (L ⊗[K] v.adicCompletion K)ˣ)
    (hint : ∀ᶠ v in Filter.cofinite,
      ((zf v : (L ⊗[K] v.adicCompletion K)ˣ) : L ⊗[K] v.adicCompletion K) ∈ semiLocalIntegers K L v ∧
      (((zf v)⁻¹ : (L ⊗[K] v.adicCompletion K)ˣ) : L ⊗[K] v.adicCompletion K) ∈
        semiLocalIntegers K L v) :
    ∃ z : (L ⊗[K] AdeleRing (𝓞 K) K)ˣ,
      compArch K L (z : L ⊗[K] AdeleRing (𝓞 K) K) = za ∧
      ∀ v, compFin K L v (z : L ⊗[K] AdeleRing (𝓞 K) K) = zf v := by
  have hden := eventually_coord_mem_of_mem_semiLocalIntegers K L
  have hE : ∀ k, ∀ᶠ v : HeightOneSpectrum (𝓞 K) in Filter.cofinite,
      coord K L (v.adicCompletion K) ((zf v : (L ⊗[K] v.adicCompletion K)ˣ) : L ⊗[K] v.adicCompletion K) k
        ∈ v.adicCompletionIntegers K := by
    intro k
    filter_upwards [hint, hden] with v h1 h2
    exact h2 _ h1.1 k
  have hE' : ∀ k, ∀ᶠ v : HeightOneSpectrum (𝓞 K) in Filter.cofinite,
      coord K L (v.adicCompletion K)
        (((zf v)⁻¹ : (L ⊗[K] v.adicCompletion K)ˣ) : L ⊗[K] v.adicCompletion K) k
        ∈ v.adicCompletionIntegers K := by
    intro k
    filter_upwards [hint, hden] with v h1 h2
    exact h2 _ h1.2 k
  obtain ⟨D, hDa, hDf⟩ := exists_comp_eq K L (za : L ⊗[K] InfiniteAdeleRing K)
    (fun v => ((zf v : (L ⊗[K] v.adicCompletion K)ˣ) : L ⊗[K] v.adicCompletion K)) hE
  obtain ⟨D', hD'a, hD'f⟩ := exists_comp_eq K L
    ((za⁻¹ : (L ⊗[K] InfiniteAdeleRing K)ˣ) : L ⊗[K] InfiniteAdeleRing K)
    (fun v => (((zf v)⁻¹ : (L ⊗[K] v.adicCompletion K)ˣ) : L ⊗[K] v.adicCompletion K)) hE'
  have h1 : D * D' = 1 := by
    apply eq_of_comp_eq K L
    · rw [map_mul, map_one, hDa, hD'a, Units.mul_inv]
    · intro v; rw [map_mul, map_one, hDf, hD'f, Units.mul_inv]
  have h2 : D' * D = 1 := by
    apply eq_of_comp_eq K L
    · rw [map_mul, map_one, hDa, hD'a, Units.inv_mul]
    · intro v; rw [map_mul, map_one, hDf, hD'f, Units.inv_mul]
  exact ⟨⟨D, D', h1, h2⟩, hDa, hDf⟩

omit [FiniteDimensional K L] in

theorem eventually_forall_ramificationIdx_eq_one :
    ∀ᶠ v : HeightOneSpectrum (𝓞 K) in Filter.cofinite,
      ∀ w : HeightOneSpectrum (𝓞 L), HeightOneSpectrum.under (𝓞 K) w = v →
        Ideal.ramificationIdx' (HeightOneSpectrum.under (𝓞 K) w).asIdeal w.asIdeal = 1 := by
  letI : Algebra (FractionRing (𝓞 K)) (FractionRing (𝓞 L)) := FractionRing.liftAlgebra _ _
  have hsep : Algebra.IsSeparable (FractionRing (𝓞 K)) (FractionRing (𝓞 L)) :=
    Algebra.IsAlgebraic.isSeparable_of_perfectField
  have hram : {w : HeightOneSpectrum (𝓞 L) |
      Ideal.ramificationIdx' (HeightOneSpectrum.under (𝓞 K) w).asIdeal w.asIdeal ≠ 1}.Finite := by
    refine (Ideal.finite_factors (differentIdeal_ne_bot (A := 𝓞 K) (B := 𝓞 L))).subset ?_
    intro w hw
    simp only [Set.mem_setOf_eq] at hw ⊢
    by_contra hdvd
    apply hw
    have hun : Algebra.IsUnramifiedAt (𝓞 K) w.asIdeal := not_dvd_differentIdeal_iff.mp hdvd
    haveI : w.asIdeal.LiesOver (HeightOneSpectrum.under (𝓞 K) w).asIdeal := ⟨rfl⟩
    rw [Ideal.ramificationIdx'_eq_ramificationIdx (p := (HeightOneSpectrum.under (𝓞 K) w).asIdeal)
      (q := w.asIdeal) (HeightOneSpectrum.under (𝓞 K) w).ne_bot]
    exact Ideal.ramificationIdx_eq_one_of_isUnramifiedAt (R := 𝓞 K) (p := w.asIdeal)
  rw [Filter.eventually_cofinite]
  refine (hram.image (HeightOneSpectrum.under (𝓞 K))).subset ?_
  intro v hv
  simp only [Set.mem_setOf_eq, not_forall] at hv
  obtain ⟨w, hwv, hw⟩ := hv
  exact ⟨w, hw, hwv⟩

end Adelic

end AutomorphicForm.ScalarNormGluing
p2m_reactivate "P2MW.S_AutomorphicForm_exists_normString_scalar_eq_toTensorGL_centralScalar_of_forall_of_finrank_ne_two.AutomorphicForm P2MW.S_AutomorphicForm_exists_normString_scalar_eq_toTensorGL_centralScalar_of_forall_of_finrank_ne_two.AutomorphicForm.ScalarNormGluing"
p2m_reactivate "P2MW.S_AutomorphicForm_exists_normString_scalar_eq_toTensorGL_centralScalar_of_forall_of_finrank_ne_two.AutomorphicForm"

end
p2m_reactivate "P2MW.S_AutomorphicForm_exists_normString_scalar_eq_toTensorGL_centralScalar_of_forall_of_finrank_ne_two.AutomorphicForm P2MW.S_AutomorphicForm_exists_normString_scalar_eq_toTensorGL_centralScalar_of_forall_of_finrank_ne_two.AutomorphicForm.ScalarNormGluing"

open _root_.AutomorphicForm _root_.P2MW.S_AutomorphicForm_exists_normString_scalar_eq_toTensorGL_centralScalar_of_forall_of_finrank_ne_two.AutomorphicForm AutomorphicForm.ScalarNormGluing in
theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (hprime : (Module.finrank K L).Prime) (hodd : Module.finrank K L ≠ 2)
    (σ : L ≃ₐ[K] L) (hσ : σ ≠ 1)
    (u : (AdeleRing (𝓞 K) K)ˣ)
    (hloc : ∀ v : HeightOneSpectrum (𝓞 K), ∃ z : (L ⊗[K] v.adicCompletion K)ˣ,
      AutomorphicForm.normString K L (v.adicCompletion K) σ
          (Matrix.GeneralLinearGroup.scalar (Fin 2) z) =
        AutomorphicForm.toTensorGL K L (v.adicCompletion K)
          (AdelicLevel.finComponent (𝓞 K) K v
            (AdelicLevel.glFin (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K u)))) :
    ∃ z : (L ⊗[K] AdeleRing (𝓞 K) K)ˣ,
      AutomorphicForm.normString K L (AdeleRing (𝓞 K) K) σ
          (Matrix.GeneralLinearGroup.scalar (Fin 2) z) =
        AutomorphicForm.toTensorGL K L (AdeleRing (𝓞 K) K)
          (AutomorphicForm.centralScalar (𝓞 K) K u) := by
  classical
  haveI : FiniteDimensional K L := Module.finite_of_finrank_pos hprime.pos
  have hodd' : Odd (Module.finrank K L) := hprime.odd_of_ne_two hodd

  let uf : ∀ v : HeightOneSpectrum (𝓞 K), (v.adicCompletion K)ˣ :=
    fun v => Units.map (piFin K v : AdeleRing (𝓞 K) K →* v.adicCompletion K) u
  have huf : ∀ v, AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K (centralScalar (𝓞 K) K u)) =
      Matrix.GeneralLinearGroup.scalar (Fin 2) (uf v) := by
    intro v
    show Matrix.GeneralLinearGroup.map (AdelicLevel.finAdeleEval (𝓞 K) K v)
        (Matrix.GeneralLinearGroup.map (AdelicLevel.adeleFin (𝓞 K) K)
          (Matrix.GeneralLinearGroup.scalar (Fin 2) u)) = _
    rw [glmap_scalar, glmap_scalar]
    congr 1

  have hgood : ∀ᶠ v : HeightOneSpectrum (𝓞 K) in Filter.cofinite,
      ((u : AdeleRing (𝓞 K) K).2 v ∈ v.adicCompletionIntegers K ∧
        ((u⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 v ∈ v.adicCompletionIntegers K) ∧
      (∀ w : HeightOneSpectrum (𝓞 L), HeightOneSpectrum.under (𝓞 K) w = v →
        Ideal.ramificationIdx' (HeightOneSpectrum.under (𝓞 K) w).asIdeal w.asIdeal = 1) :=
    (((u : AdeleRing (𝓞 K) K).2.2).and (((u⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2.2)).and
      (eventually_forall_ramificationIdx_eq_one K L)

  have hloc' : ∀ v : HeightOneSpectrum (𝓞 K), ∃ zv : (L ⊗[K] v.adicCompletion K)ˣ,
      normString K L (v.adicCompletion K) σ (Matrix.GeneralLinearGroup.scalar (Fin 2) zv) =
        toTensorGL K L (v.adicCompletion K)
          (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K (centralScalar (𝓞 K) K u))) ∧
      ((((u : AdeleRing (𝓞 K) K).2 v ∈ v.adicCompletionIntegers K ∧
          ((u⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 v ∈ v.adicCompletionIntegers K) ∧
        (∀ w : HeightOneSpectrum (𝓞 L), HeightOneSpectrum.under (𝓞 K) w = v →
          Ideal.ramificationIdx' (HeightOneSpectrum.under (𝓞 K) w).asIdeal w.asIdeal = 1)) →
        (zv : L ⊗[K] v.adicCompletion K) ∈ semiLocalIntegers K L v ∧
        ((zv⁻¹ : (L ⊗[K] v.adicCompletion K)ˣ) : L ⊗[K] v.adicCompletion K) ∈ semiLocalIntegers K L v) := by
    intro v
    by_cases hg :
      (((u : AdeleRing (𝓞 K) K).2 v ∈ v.adicCompletionIntegers K ∧
          ((u⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 v ∈ v.adicCompletionIntegers K) ∧
        (∀ w : HeightOneSpectrum (𝓞 L), HeightOneSpectrum.under (𝓞 K) w = v →
          Ideal.ramificationIdx' (HeightOneSpectrum.under (𝓞 K) w).asIdeal w.asIdeal = 1))
    · obtain ⟨zv, h1, h2, h3⟩ :=
        exists_units_normString_scalar_of_unramified K L hprime σ hσ v hg.2 (uf v) hg.1.1 hg.1.2
      exact ⟨zv, by rw [huf]; exact h3, fun _ => ⟨h1, h2⟩⟩
    · obtain ⟨zv, hzv⟩ := hloc v
      exact ⟨zv, hzv, fun h => absurd h hg⟩
  choose zf hNf hint using hloc'

  obtain ⟨za, hNa⟩ := exists_arch K L σ hodd' hprime.ne_zero u

  obtain ⟨z, hza, hzf⟩ := units_exists_comp_eq K L za zf (hgood.mono fun v hv => hint v hv)
  refine ⟨z, ?_⟩
  apply gl_eq_of_comp_eq K L
  · have hz : Units.map ((compArch K L).toRingHom : L ⊗[K] AdeleRing (𝓞 K) K →* L ⊗[K] InfiniteAdeleRing K) z
        = za := Units.ext hza
    rw [glmap_compArch_normString, glmap_scalar, hz, hNa, glmap_compArch_toTensorGL]
  · intro v
    have hz : Units.map ((compFin K L v).toRingHom : L ⊗[K] AdeleRing (𝓞 K) K →* L ⊗[K] v.adicCompletion K) z
        = zf v := Units.ext (hzf v)
    rw [glmap_compFin_normString, glmap_scalar, hz, hNf v, glmap_compFin_toTensorGL]

end S_AutomorphicForm_exists_normString_scalar_eq_toTensorGL_centralScalar_of_forall_of_finrank_ne_two
end P2MW
export P2MW.S_AutomorphicForm_exists_normString_scalar_eq_toTensorGL_centralScalar_of_forall_of_finrank_ne_two (solution)
