-- Prove2me | solution 1 for AutomorphicForm.exists_linearMap_mul_sigmaTensor_sub_mul_and_det_eq_neg_one_pow_mul_norm_sub_norm
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/a5bcd64c-69ad-55e8-8ec4-9d52ff8a667e

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_LanglandsTunnell_CubicInduction_TorusValues
import Definitions.Def_AutomorphicForm_ConstantTerm
import Theorems.Thm_Algebra_TensorProduct_algebraMap_norm_eq_prod_congr_apply_of_isGalois
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

p2m_attr_erase "ext" "IsDedekindDomain.HeightOneSpectrum.adicCompletion.ext"
namespace P2MW.S_AutomorphicForm_exists_linearMap_mul_sigmaTensor_sub_mul_and_det_eq_neg_one_pow_mul_norm_sub_norm

set_option autoImplicit false

open MeasureTheory NumberField IsDedekindDomain
open scoped TensorProduct TensorProduct.RightActions ENNReal Pointwise
open LanglandsTunnell.CubicInduction (diagUnits2)

set_option autoImplicit false
open NumberField IsDedekindDomain Polynomial
open scoped TensorProduct TensorProduct.RightActions

noncomputable section

namespace Ws35H
namespace Jac

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
variable {v : HeightOneSpectrum (𝓞 K)}

local notation "F" => v.adicCompletion K
local notation "E" => L ⊗[K] v.adicCompletion K
local notation "ℓ" => Module.finrank K L

attribute [local instance 9999] Algebra.toModule

theorem isScalarTower_FEE : IsScalarTower F E E :=
  @IsScalarTower.right F E _ _ (TensorProduct.RightActions.instAlgebra_definitions K (v.adicCompletion K) L)
theorem smulCommClass_FEE : SMulCommClass F E E :=
  @Algebra.to_smulCommClass F E _ _ (TensorProduct.RightActions.instAlgebra_definitions K (v.adicCompletion K) L)
theorem finite_KL : Module.Finite K L := Module.Finite.of_restrictScalars_finite ℚ K L

attribute [local instance] isScalarTower_FEE smulCommClass_FEE finite_KL

theorem finrank_E : Module.finrank F E = ℓ := TensorProduct.finrank_rightAlgebra L

variable (σ : L ≃ₐ[K] L)

def sigmaLin : E →ₗ[F] E where
  toFun := AutomorphicForm.sigmaTensor K L F σ
  map_add' x y := map_add _ x y
  map_smul' c x := by
    rw [Algebra.smul_def, Algebra.smul_def, map_mul, RingHom.id_apply]
    congr 1
    show (Algebra.TensorProduct.map σ.toAlgHom (AlgHom.id K F)) ((1 : L) ⊗ₜ[K] c) = (1 : L) ⊗ₜ[K] c
    rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
    simp

omit [NumberField L] in
@[scoped simp] theorem sigmaLin_apply (x : E) : sigmaLin (v := v) σ x = AutomorphicForm.sigmaTensor K L F σ x := rfl

omit [NumberField L] in
theorem sigmaTensor_tmul (τ : L ≃ₐ[K] L) (l : L) (c : F) :
    AutomorphicForm.sigmaTensor K L F τ (l ⊗ₜ[K] c) = τ l ⊗ₜ[K] c := by
  show (Algebra.TensorProduct.map τ.toAlgHom (AlgHom.id K F)) (l ⊗ₜ[K] c) = τ l ⊗ₜ[K] c
  rw [Algebra.TensorProduct.map_tmul]; rfl

omit [NumberField L] in
theorem sigmaTensor_iterate (i : ℕ) (x : E) :
    (AutomorphicForm.sigmaTensor K L F σ)^[i] x = AutomorphicForm.sigmaTensor K L F (σ ^ i) x := by
  induction i generalizing x with
  | zero =>
      simp only [Function.iterate_zero, id_eq, pow_zero]
      induction x using TensorProduct.induction_on with
      | zero => simp
      | tmul l c => rw [sigmaTensor_tmul]; rfl
      | add x y hx hy => rw [map_add, ← hx, ← hy]
  | succ i ih =>
      rw [Function.iterate_succ_apply', ih]
      induction x using TensorProduct.induction_on with
      | zero => simp
      | tmul l c => rw [sigmaTensor_tmul, sigmaTensor_tmul, sigmaTensor_tmul, pow_succ', AlgEquiv.mul_apply]
      | add x y hx hy => rw [map_add, map_add, map_add, hx, hy]

omit [NumberField L] in
theorem sigmaLin_pow_apply (i : ℕ) (x : E) :
    (sigmaLin (v := v) σ ^ i) x = AutomorphicForm.sigmaTensor K L F (σ ^ i) x := by
  rw [Module.End.pow_apply, show (⇑(sigmaLin (v := v) σ))^[i] x = (AutomorphicForm.sigmaTensor K L F σ)^[i] x from rfl,
    sigmaTensor_iterate]

omit [NumberField L] in
theorem sigmaTensor_one (x : E) : AutomorphicForm.sigmaTensor K L F (1 : L ≃ₐ[K] L) x = x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul l c => rw [sigmaTensor_tmul]; rfl
  | add x y hx hy => rw [map_add, hx, hy]

section Galois

variable [IsGalois K L] (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
include hgen

theorem orderOf_eq : orderOf σ = ℓ :=
  (orderOf_eq_card_of_forall_mem_zpowers hgen).trans (IsGalois.card_aut_eq_finrank K L)

theorem sigmaLin_pow_finrank : sigmaLin (v := v) σ ^ ℓ = 1 := by
  ext x
  rw [sigmaLin_pow_apply, ← orderOf_eq σ hgen, pow_orderOf_eq_one, sigmaTensor_one]
  rfl

theorem prod_range_pow_eq_prod_univ {M : Type*} [CommMonoid M] (f : (L ≃ₐ[K] L) → M) :
    ∏ i ∈ Finset.range ℓ, f (σ ^ i) = ∏ τ : L ≃ₐ[K] L, f τ := by
  classical
  have hord := orderOf_eq σ hgen
  have hinj : Set.InjOn (fun i : ℕ => σ ^ i) ↑(Finset.range ℓ) := by
    rw [Finset.coe_range, ← hord]; exact pow_injOn_Iio_orderOf
  have himg : (Finset.range ℓ).image (fun i : ℕ => σ ^ i) = Finset.univ := by
    apply Finset.eq_univ_of_card
    rw [Finset.card_image_of_injOn hinj, Finset.card_range, ← hord, orderOf_eq_card_of_forall_mem_zpowers hgen,
      Nat.card_eq_fintype_card]
  rw [← himg, Finset.prod_image hinj]

theorem algebraMap_norm_eq_prod (x : E) :
    algebraMap F E (Algebra.norm F x) = ∏ i ∈ Finset.range ℓ, (sigmaLin (v := v) σ ^ i) x := by
  rw [Algebra.TensorProduct.algebraMap_norm_eq_prod_congr_apply_of_isGalois K L F x,
    ← prod_range_pow_eq_prod_univ σ hgen (fun τ => Algebra.TensorProduct.congr τ
      (AlgEquiv.refl : F ≃ₐ[K] F) x)]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [sigmaLin_pow_apply]
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul l c => rw [sigmaTensor_tmul, Algebra.TensorProduct.congr_apply, Algebra.TensorProduct.map_tmul]; rfl
  | add x y hx hy => rw [map_add, map_add, hx, hy]

end Galois

def T (c : E) : E →ₗ[F] E := (Algebra.lmul F E c) ∘ₗ sigmaLin (v := v) σ

omit [NumberField L] in
@[scoped simp] theorem T_apply (c x : E) : T (v := v) σ c x = c * AutomorphicForm.sigmaTensor K L F σ x := by
  simp [T, Algebra.coe_lmul_eq_mul]

omit [NumberField L] in
theorem T_pow_apply (c : E) (i : ℕ) (x : E) :
    (T (v := v) σ c ^ i) x = (∏ j ∈ Finset.range i, (sigmaLin (v := v) σ ^ j) c) * (sigmaLin (v := v) σ ^ i) x := by
  induction i generalizing x with
  | zero => simp
  | succ i ih =>
      rw [pow_succ', Module.End.mul_apply, ih, T_apply, map_mul, Finset.prod_range_succ', pow_zero,
        Module.End.one_apply, map_prod]
      have h1 : ∀ j, AutomorphicForm.sigmaTensor K L F σ ((sigmaLin (v := v) σ ^ j) c) =
          (sigmaLin (v := v) σ ^ (j + 1)) c := by
        intro j; rw [pow_succ', Module.End.mul_apply, sigmaLin_apply]
      have h2 : AutomorphicForm.sigmaTensor K L F σ ((sigmaLin (v := v) σ ^ i) x) =
          (sigmaLin (v := v) σ ^ (i + 1)) x := by
        rw [pow_succ', Module.End.mul_apply, sigmaLin_apply]
      simp_rw [h1, h2]
      ring

section CharPoly

variable [IsGalois K L] (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
include hgen

theorem T_pow_finrank (c : E) : T (v := v) σ c ^ ℓ = Algebra.norm F c • (1 : E →ₗ[F] E) := by
  ext x
  rw [T_pow_apply, ← algebraMap_norm_eq_prod σ hgen, sigmaLin_pow_finrank σ hgen,
    LinearMap.smul_apply, Module.End.one_apply, Algebra.smul_def]

omit hgen in
omit [IsGalois K L] in
theorem nonempty_extension : Nonempty (v.Extension (𝓞 L)) := by
  by_contra h
  rw [not_nonempty_iff] at h
  have hsub : Subsingleton (Π w : v.Extension (𝓞 L), w.1.adicCompletion L) := inferInstance
  have : Subsingleton E :=
    (HeightOneSpectrum.adicCompletion.baseChangeAlgEquiv K L (𝓞 L) v).toEquiv.subsingleton
  exact not_subsingleton E this

theorem coeff_eq_zero_of_dependence (r : ℕ → F) (u : ℕ → E) (hu : ∀ i, IsUnit (u i))
    (hsum : ∀ θ : E, ∑ i ∈ Finset.range ℓ, (algebraMap F E (r i) * u i) * (sigmaLin (v := v) σ ^ i) θ = 0) :
    ∀ i, i < ℓ → r i = 0 := by
  classical
  obtain ⟨w₀⟩ := nonempty_extension (K := K) (L := L) (v := v)
  set φ := HeightOneSpectrum.adicCompletion.baseChangeAlgEquiv K L (𝓞 L) v with hφ
  set ψ : E →+* w₀.1.adicCompletion L :=
    (Pi.evalRingHom (fun w : v.Extension (𝓞 L) => w.1.adicCompletion L) w₀).comp φ.toRingEquiv.toRingHom with hψ
  have hψ_tmul : ∀ (m : L) (c : F), ψ (m ⊗ₜ[K] c) =
      algebraMap L (w₀.1.adicCompletion L) m * algebraMap F (w₀.1.adicCompletion L) c := by
    intro m c
    show φ (m ⊗ₜ[K] c) w₀ = _
    show HeightOneSpectrum.adicCompletion.baseChange K L (𝓞 L) v (m ⊗ₜ[K] c) w₀ = _
    rw [HeightOneSpectrum.adicCompletion.baseChange_tmul_apply]

  set Fm : Fin ℓ → (L →* w₀.1.adicCompletion L) := fun i =>
    (algebraMap L (w₀.1.adicCompletion L)).toMonoidHom.comp ((σ ^ (i : ℕ)).toAlgHom.toRingHom.toMonoidHom) with hFm
  have hFapply : ∀ (i : Fin ℓ) (m : L), Fm i m = algebraMap L (w₀.1.adicCompletion L) ((σ ^ (i : ℕ)) m) :=
    fun i m => rfl
  have hFinj : Function.Injective Fm := by
    intro i j hij
    apply Fin.ext
    have hord := orderOf_eq σ hgen
    apply pow_injOn_Iio_orderOf (by rw [hord]; exact i.2) (by rw [hord]; exact j.2)
    ext m
    have := congrArg (fun f : L →* w₀.1.adicCompletion L => f m) hij
    simp only [hFapply] at this
    exact (algebraMap L (w₀.1.adicCompletion L)).injective this
  have hli : LinearIndependent (w₀.1.adicCompletion L) (fun i => (⇑(Fm i) : L → w₀.1.adicCompletion L)) :=
    (linearIndependent_monoidHom L (w₀.1.adicCompletion L)).comp Fm hFinj
  have hdep : ∑ i ∈ (Finset.univ : Finset (Fin ℓ)), ψ (algebraMap F E (r i) * u i) •
      (⇑(Fm i) : L → w₀.1.adicCompletion L) = 0 := by
    funext m
    rw [Finset.sum_apply, Pi.zero_apply]
    simp only [Pi.smul_apply, hFapply, smul_eq_mul]
    have := congrArg ψ (hsum (m ⊗ₜ[K] (1 : F)))
    rw [map_zero, map_sum] at this
    rw [← this, Finset.sum_range]
    refine Finset.sum_congr rfl fun i _ => ?_
    symm
    rw [map_mul, map_mul, sigmaLin_pow_apply, sigmaTensor_tmul, hψ_tmul, map_one, mul_one]
  intro i hi
  have h0 := linearIndependent_iff'.mp hli Finset.univ (fun i => ψ (algebraMap F E (r i) * u i)) hdep ⟨i, hi⟩
    (Finset.mem_univ _)
  simp only [map_mul] at h0
  rcases mul_eq_zero.mp h0 with h1 | h1
  · have hr : ψ (algebraMap F E (r i)) = algebraMap F (w₀.1.adicCompletion L) (r i) := by
      rw [Algebra.algebraMap_eq_smul_one, Algebra.smul_def]
      show ψ (algebraMap F E (r i) * 1) = _
      rw [mul_one]
      show ψ ((1 : L) ⊗ₜ[K] r i) = _
      rw [hψ_tmul, map_one, one_mul]
    rw [hr] at h1
    exact (map_eq_zero_iff _ (algebraMap F (w₀.1.adicCompletion L)).injective).mp h1
  · exfalso; exact ((hu i).map ψ).ne_zero h1

theorem charpoly_T {c : E} (hc : IsUnit c) :
    (T (v := v) σ c).charpoly = X ^ ℓ - C (Algebra.norm F c) := by
  set f := T (v := v) σ c with hf
  set p : F[X] := X ^ ℓ - C (Algebra.norm F c) with hp
  have hℓ : 0 < ℓ := Module.finrank_pos
  have hpm : p.Monic := by
    rw [hp]; exact Polynomial.monic_X_pow_sub_C _ hℓ.ne'
  have hpdeg : p.natDegree = ℓ := by rw [hp]; exact Polynomial.natDegree_X_pow_sub_C
  have hcm : f.charpoly.Monic := LinearMap.charpoly_monic f
  have hcdeg : f.charpoly.natDegree = ℓ := by rw [LinearMap.charpoly_natDegree, finrank_E]
  have h1 : aeval f f.charpoly = 0 := LinearMap.aeval_self_charpoly f
  have h2 : aeval f p = 0 := by
    rw [hp, map_sub, map_pow, aeval_X, aeval_C, hf, T_pow_finrank σ hgen, Algebra.algebraMap_eq_smul_one,
      sub_self]
  set r := f.charpoly - p with hr
  have hr0 : aeval f r = 0 := by rw [hr, map_sub, h1, h2, sub_self]
  have hrdeg : r.natDegree < ℓ := by
    by_cases hr00 : r = 0
    · rw [hr00, natDegree_zero]; exact hℓ
    have hdeg' : r.degree < f.charpoly.degree := by
      rw [hr]
      apply Polynomial.degree_sub_lt
      · rw [Polynomial.degree_eq_natDegree hcm.ne_zero, Polynomial.degree_eq_natDegree hpm.ne_zero, hcdeg, hpdeg]
      · exact hcm.ne_zero
      · rw [hcm.leadingCoeff, hpm.leadingCoeff]
    have := Polynomial.natDegree_lt_natDegree hr00 hdeg'
    rwa [hcdeg] at this
  suffices hrz : r = 0 by
    have : f.charpoly = p := sub_eq_zero.1 (by rw [← hr, hrz])
    rw [this]
  have hsum : ∀ x : E, ∑ i ∈ Finset.range ℓ, r.coeff i • (f ^ i) x = 0 := by
    intro x
    have := congrArg (fun g : E →ₗ[F] E => g x) hr0
    simp only [LinearMap.zero_apply] at this
    rw [Polynomial.aeval_eq_sum_range' hrdeg] at this
    simpa [LinearMap.sum_apply, LinearMap.smul_apply] using this

  have hu : ∀ i, IsUnit (∏ j ∈ Finset.range i, (sigmaLin (v := v) σ ^ j) c) := by
    intro i
    refine IsUnit.prod_iff.mpr fun j _ => ?_
    rw [sigmaLin_pow_apply]
    exact hc.map _
  have hcoeff := coeff_eq_zero_of_dependence σ hgen (fun i => r.coeff i)
    (fun i => ∏ j ∈ Finset.range i, (sigmaLin (v := v) σ ^ j) c) hu (by
      intro θ
      rw [← hsum θ]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [hf, T_pow_apply]
      rw [mul_assoc, ← Algebra.smul_def])
  ext i : 1
  rw [coeff_zero]
  by_cases hi : i < ℓ
  · exact hcoeff i hi
  · exact Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_lt_of_le hrdeg (not_lt.1 hi))

theorem det_one_sub_T {c : E} (hc : IsUnit c) :
    LinearMap.det ((1 : E →ₗ[F] E) - T (v := v) σ c) = 1 - Algebra.norm F c := by
  classical
  set b := Module.finBasis F E
  have h1 : LinearMap.det ((1 : E →ₗ[F] E) - T (v := v) σ c) =
      (LinearMap.toMatrix b b ((1 : E →ₗ[F] E) - T (v := v) σ c)).det := (LinearMap.det_toMatrix b _).symm
  have h3 : LinearMap.toMatrix b b ((1 : E →ₗ[F] E) - T (v := v) σ c) =
      LinearMap.toMatrix b b (1 : E →ₗ[F] E) - LinearMap.toMatrix b b (T (v := v) σ c) :=
    map_sub (LinearMap.toMatrix b b) _ _
  rw [h1, h3, show LinearMap.toMatrix b b (1 : E →ₗ[F] E) = 1 from LinearMap.toMatrix_one b]
  have h2 := Matrix.eval_charpoly (LinearMap.toMatrix b b (T (v := v) σ c)) 1
  rw [LinearMap.charpoly_toMatrix, charpoly_T σ hgen hc] at h2
  simp only [eval_sub, eval_pow, eval_X, one_pow, eval_C] at h2
  rw [h2, map_one]

omit hgen in
omit [IsGalois K L] in

def S (a b : E) : E →ₗ[F] E := T (v := v) σ a - Algebra.lmul F E b

omit hgen in
omit [IsGalois K L] [NumberField L] in
@[scoped simp] theorem S_apply (a b x : E) :
    S (v := v) σ a b x = a * AutomorphicForm.sigmaTensor K L F σ x - b * x := by
  simp [S, Algebra.coe_lmul_eq_mul]

theorem det_S (a b : Eˣ) :
    LinearMap.det (S (v := v) σ (a : E) (b : E)) = (-1) ^ ℓ * (Algebra.norm F (b : E) - Algebra.norm F (a : E)) := by
  classical
  have hbu : (b : E) * (↑b⁻¹ : E) = 1 := Units.mul_inv b
  have hS : S (v := v) σ (a : E) (b : E) =
      Algebra.lmul F E (-(b : E)) ∘ₗ ((1 : E →ₗ[F] E) - T (v := v) σ ((↑b⁻¹ : E) * a)) := by
    ext x
    rw [S_apply, LinearMap.comp_apply, LinearMap.sub_apply, Module.End.one_apply, T_apply,
      Algebra.coe_lmul_eq_mul, LinearMap.mul_apply']
    have : -(b : E) * (x - (↑b⁻¹ : E) * a * AutomorphicForm.sigmaTensor K L F σ x) =
        ((b : E) * (↑b⁻¹ : E)) * a * AutomorphicForm.sigmaTensor K L F σ x - b * x := by ring
    rw [this, hbu, one_mul]
  have hcu : IsUnit ((↑b⁻¹ : E) * a) := (Units.isUnit b⁻¹).mul (Units.isUnit a)
  rw [hS, LinearMap.det_comp, det_one_sub_T σ hgen hcu, ← Algebra.norm_apply, map_mul]
  have h1 : Algebra.norm F (b : E) * Algebra.norm F (↑b⁻¹ : E) = 1 := by rw [← map_mul, hbu, map_one]
  have h2 : Algebra.norm F (-(b : E)) = (-1) ^ ℓ * Algebra.norm F (b : E) := by
    have hneg : (-(b : E)) = (-1 : E) * (b : E) := by ring
    rw [hneg, map_mul, show (-1 : E) = algebraMap F E (-1) by rw [map_neg, map_one],
      Algebra.norm_algebraMap, finrank_E]
  rw [h2]
  calc (-1) ^ ℓ * Algebra.norm F (b : E) * (1 - Algebra.norm F (↑b⁻¹ : E) * Algebra.norm F (a : E))
      = (-1) ^ ℓ * (Algebra.norm F (b : E) - (Algebra.norm F (b : E) * Algebra.norm F (↑b⁻¹ : E)) * Algebra.norm F (a : E)) := by ring
    _ = (-1) ^ ℓ * (Algebra.norm F (b : E) - Algebra.norm F (a : E)) := by rw [h1, one_mul]

theorem main (A B : Eˣ) :
    ∃ Tm : E →ₗ[F] E,
      (∀ x, Tm x = (A : E) * AutomorphicForm.sigmaTensor K L F σ x - (B : E) * x) ∧
      LinearMap.det Tm = (-1) ^ ℓ * (Algebra.norm F (B : E) - Algebra.norm F (A : E)) :=
  ⟨S (v := v) σ (A : E) (B : E), fun x => S_apply σ _ _ x, det_S σ hgen A B⟩

end CharPoly

end Ws35H.Jac
p2m_reactivate "P2MW.S_AutomorphicForm_exists_linearMap_mul_sigmaTensor_sub_mul_and_det_eq_neg_one_pow_mul_norm_sub_norm.Ws35H P2MW.S_AutomorphicForm_exists_linearMap_mul_sigmaTensor_sub_mul_and_det_eq_neg_one_pow_mul_norm_sub_norm.Ws35H.Jac"
p2m_reactivate "P2MW.S_AutomorphicForm_exists_linearMap_mul_sigmaTensor_sub_mul_and_det_eq_neg_one_pow_mul_norm_sub_norm.Ws35H"

theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (v : HeightOneSpectrum (𝓞 K)) (A B : (L ⊗[K] v.adicCompletion K)ˣ) :
    ∃ T : (L ⊗[K] v.adicCompletion K) →ₗ[v.adicCompletion K] (L ⊗[K] v.adicCompletion K),
      (∀ x, T x = (A : L ⊗[K] v.adicCompletion K) * AutomorphicForm.sigmaTensor K L (v.adicCompletion K) σ x -
        (B : L ⊗[K] v.adicCompletion K) * x) ∧
      LinearMap.det T = (-1) ^ Module.finrank K L *
        (Algebra.norm (v.adicCompletion K) (B : L ⊗[K] v.adicCompletion K) -
          Algebra.norm (v.adicCompletion K) (A : L ⊗[K] v.adicCompletion K)) :=
  Ws35H.Jac.main (K := K) (L := L) (v := v) σ hgen A B

end
end S_AutomorphicForm_exists_linearMap_mul_sigmaTensor_sub_mul_and_det_eq_neg_one_pow_mul_norm_sub_norm
end P2MW
export P2MW.S_AutomorphicForm_exists_linearMap_mul_sigmaTensor_sub_mul_and_det_eq_neg_one_pow_mul_norm_sub_norm (solution)
