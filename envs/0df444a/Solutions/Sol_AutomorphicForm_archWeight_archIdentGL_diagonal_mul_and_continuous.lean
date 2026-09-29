-- Prove2me | solution 1 for AutomorphicForm.archWeight_archIdentGL_diagonal_mul_and_continuous
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/ce92968d-a093-545d-8974-bb928283c5b5

import Definitions.Def_AutomorphicForm_BaseChangePlaces
import Definitions.Def_AutomorphicForm_WeightedOrbitalRelation
import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_NumberField_AdelicHeight
import Definitions.Def_AutomorphicForm_WeylIntertwining
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

p2m_attr_erase "ext" "NumberField.InfinitePlace.Completion.ext"
namespace P2MW.S_AutomorphicForm_archWeight_archIdentGL_diagonal_mul_and_continuous

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar IsDedekindDomain
open scoped TensorProduct TensorProduct.RightActions

namespace ArchWeightDiagL

open AutomorphicForm AutomorphicForm.WindowedSiegel NumberField.AdelicLevel

theorem val_archComponent_adelicWeyl (L : Type) [Field L] [NumberField L] (w : NumberField.InfinitePlace L) :
    ((NumberField.AdelicLevel.archComponent L w
        (AdelicLevel.glArch (𝓞 L) L (AutomorphicForm.adelicWeyl (𝓞 L) L)) : GL (Fin 2) w.Completion) :
      Matrix (Fin 2) (Fin 2) w.Completion) = !![0, 1; 1, 0] := by
  ext i j
  rw [NumberField.AdelicLevel.archComponent_apply, NumberField.AdelicLevel.glArch_apply]
  change (algebraMap L (AdeleRing (𝓞 L) L)
      (((AutomorphicForm.gl2Weyl : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) i j)).1 w = !![0, 1; 1, 0] i j
  have hval : ((AutomorphicForm.gl2Weyl : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) = !![0, 1; 1, 0] := rfl
  rw [hval]
  fin_cases i <;> fin_cases j <;> simp <;> rfl

theorem topNormSq_pos {F : Type*} [NormedField F] (g : GL (Fin 2) F) :
    0 < topNormSq (g : Matrix (Fin 2) (Fin 2) F) := by
  unfold topNormSq
  rcases eq_or_ne ((g : Matrix (Fin 2) (Fin 2) F) 0 0) 0 with h0 | h0
  · rcases eq_or_ne ((g : Matrix (Fin 2) (Fin 2) F) 0 1) 0 with h1 | h1
    · exact absurd (by rw [Matrix.det_fin_two, h0, h1]; ring) (Matrix.GeneralLinearGroup.det_ne_zero g)
    · exact add_pos_of_nonneg_of_pos (sq_nonneg _) (pow_pos (norm_pos_iff.2 h1) 2)
  · exact add_pos_of_pos_of_nonneg (pow_pos (norm_pos_iff.2 h0) 2) (sq_nonneg _)

theorem rowNormSq_swap_mul {F : Type*} [NormedField F] (M : Matrix (Fin 2) (Fin 2) F) :
    rowNormSq (!![(0 : F), 1; 1, 0] * M) = topNormSq M := by
  simp [rowNormSq, topNormSq, Matrix.mul_apply, Fin.sum_univ_two]

theorem det_swap {F : Type*} [NormedField F] : (!![(0 : F), 1; 1, 0]).det = -1 := by
  simp [Matrix.det_fin_two]

theorem continuous_localHeight' {F : Type*} [NormedField F] :
    Continuous fun g : GL (Fin 2) F => localHeight g := by
  have h1 : Continuous fun g : GL (Fin 2) F => ‖(g : Matrix (Fin 2) (Fin 2) F).det‖ :=
    (Units.continuous_val.matrix_det).norm
  have h2 : Continuous fun g : GL (Fin 2) F => rowNormSq (g : Matrix (Fin 2) (Fin 2) F) := by
    unfold rowNormSq
    exact (((Units.continuous_val.matrix_elem 1 0).norm).pow 2).add
      (((Units.continuous_val.matrix_elem 1 1).norm).pow 2)
  exact h1.div h2 fun g => (rowNormSq_pos g).ne'

theorem localHeight_diag_mul_mul_localHeight_swap_mul {F : Type*} [NormedField F]
    (S T X : GL (Fin 2) F) (hS : (S : Matrix (Fin 2) (Fin 2) F) = !![0, 1; 1, 0])
    (hT01 : (T : Matrix (Fin 2) (Fin 2) F) 0 1 = 0) (hT10 : (T : Matrix (Fin 2) (Fin 2) F) 1 0 = 0) :
    localHeight (T * X) * localHeight (S * (T * X)) = localHeight X * localHeight (S * X) := by
  have hdetT : (T : Matrix (Fin 2) (Fin 2) F).det =
      (T : Matrix (Fin 2) (Fin 2) F) 0 0 * (T : Matrix (Fin 2) (Fin 2) F) 1 1 := by
    rw [Matrix.det_fin_two, hT01, hT10]; ring
  have ha : (T : Matrix (Fin 2) (Fin 2) F) 0 0 ≠ 0 := by
    intro h; exact Matrix.GeneralLinearGroup.det_ne_zero T (by rw [hdetT, h, zero_mul])
  have hb : (T : Matrix (Fin 2) (Fin 2) F) 1 1 ≠ 0 := by
    intro h; exact Matrix.GeneralLinearGroup.det_ne_zero T (by rw [hdetT, h, mul_zero])
  have hrowTX : rowNormSq ((T * X : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
      ‖(T : Matrix (Fin 2) (Fin 2) F) 1 1‖ ^ 2 * rowNormSq (X : Matrix (Fin 2) (Fin 2) F) :=
    rowNormSq_scalar_entries_mul hT10 rfl X
  have htopTX : topNormSq ((T * X : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
      ‖(T : Matrix (Fin 2) (Fin 2) F) 0 0‖ ^ 2 * topNormSq (X : Matrix (Fin 2) (Fin 2) F) :=
    topNormSq_scalar_entries_mul rfl hT01 X
  have hrowSTX : rowNormSq ((S * (T * X) : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
      topNormSq ((T * X : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) := by
    rw [Units.val_mul, hS, rowNormSq_swap_mul]
  have hrowSX : rowNormSq ((S * X : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
      topNormSq (X : Matrix (Fin 2) (Fin 2) F) := by
    rw [Units.val_mul, hS, rowNormSq_swap_mul]
  have hdTX : ‖((T * X : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F).det‖ =
      ‖(T : Matrix (Fin 2) (Fin 2) F) 0 0‖ * ‖(T : Matrix (Fin 2) (Fin 2) F) 1 1‖ *
        ‖(X : Matrix (Fin 2) (Fin 2) F).det‖ := by
    rw [Units.val_mul, Matrix.det_mul, hdetT, norm_mul, norm_mul]
  have hdSTX : ‖((S * (T * X) : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F).det‖ =
      ‖((T * X : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F).det‖ := by
    rw [Units.val_mul, Matrix.det_mul, hS, det_swap, norm_mul, norm_neg, norm_one, one_mul]
  have hdSX : ‖((S * X : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F).det‖ =
      ‖(X : Matrix (Fin 2) (Fin 2) F).det‖ := by
    rw [Units.val_mul, Matrix.det_mul, hS, det_swap, norm_mul, norm_neg, norm_one, one_mul]
  have hr := rowNormSq_pos X
  have ht := topNormSq_pos X
  have hna : 0 < ‖(T : Matrix (Fin 2) (Fin 2) F) 0 0‖ := norm_pos_iff.2 ha
  have hnb : 0 < ‖(T : Matrix (Fin 2) (Fin 2) F) 1 1‖ := norm_pos_iff.2 hb
  unfold localHeight
  rw [hdSTX, hdTX, hrowSTX, hrowTX, htopTX, hdSX, hrowSX]
  field_simp

theorem algEquiv_pow_finrank_eq_one {F E : Type*} [Field F] [Field E] [Algebra F E] [FiniteDimensional F E]
    (τ : E ≃ₐ[F] E) : τ ^ Module.finrank F E = 1 := by
  apply orderOf_dvd_iff_pow_eq_one.mp
  refine (orderOf_dvd_natCard τ).trans ?_
  have h := IntermediateField.finrank_fixedField_eq_card (⊤ : Subgroup (E ≃ₐ[F] E))
  rw [Subgroup.card_top] at h
  refine ⟨Module.finrank F (IntermediateField.fixedField (⊤ : Subgroup (E ≃ₐ[F] E))), ?_⟩
  rw [← h, mul_comm]
  exact (Module.finrank_mul_finrank F (IntermediateField.fixedField (⊤ : Subgroup (E ≃ₐ[F] E))) E).symm

section Sigma

variable (K L : Type) [Field K] [Field L] [Algebra K L] (A : Type) [CommRing A] [Algebra K A]

theorem sigmaTensor_mul_apply (τ₁ τ₂ : L ≃ₐ[K] L) (z : L ⊗[K] A) :
    sigmaTensor K L A (τ₁ * τ₂) z = sigmaTensor K L A τ₁ (sigmaTensor K L A τ₂ z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul l a => rfl
  | add x y hx hy => simp only [map_add, hx, hy]

theorem sigmaTensor_one_apply (z : L ⊗[K] A) : sigmaTensor K L A 1 z = z := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul l a => rfl
  | add x y hx hy => simp only [map_add, hx, hy]

theorem sigmaTensor_pow_apply (τ : L ≃ₐ[K] L) (m : ℕ) (z : L ⊗[K] A) :
    ((sigmaTensor K L A τ) ^ m) z = sigmaTensor K L A (τ ^ m) z := by
  induction m generalizing z with
  | zero => rw [pow_zero, pow_zero, RingHom.coe_one, id_eq, sigmaTensor_one_apply]
  | succ m ih => rw [pow_succ, pow_succ, RingHom.coe_mul, Function.comp_apply, ih, sigmaTensor_mul_apply]

theorem sigmaTensor_pow_finrank_apply [FiniteDimensional K L] (τ : L ≃ₐ[K] L) (z : L ⊗[K] A) :
    ((sigmaTensor K L A τ) ^ Module.finrank K L) z = z := by
  rw [sigmaTensor_pow_apply, algEquiv_pow_finrank_eq_one, sigmaTensor_one_apply]

theorem val_iterate_sigmaGL (τ : L ≃ₐ[K] L) (g : GL (Fin 2) (L ⊗[K] A)) (i : ℕ) (j k : Fin 2) :
    (((⇑(sigmaGL K L A τ))^[i] g : GL (Fin 2) (L ⊗[K] A)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) j k =
      ((sigmaTensor K L A τ) ^ i) (((g : GL (Fin 2) (L ⊗[K] A)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) j k) := by
  induction i with
  | zero => rw [Function.iterate_zero, pow_zero, RingHom.coe_one, id_eq, id_eq]
  | succ i ih =>
    rw [Function.iterate_succ_apply', pow_succ', RingHom.coe_mul, Function.comp_apply, ← ih]
    rfl

end Sigma

theorem telescope {A : Type*} [CommRing A] (s : A →+* A) (x d₀ d₁ : A) (h : x * d₁ = d₀ * s x) (m : ℕ) :
    x * ((List.range m).map fun k => (s ^ k) d₁).prod =
      ((List.range m).map fun k => (s ^ k) d₀).prod * (s ^ m) x := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [List.range_succ, List.map_append, List.map_append, List.prod_append, List.prod_append,
      List.map_singleton, List.map_singleton, List.prod_singleton, List.prod_singleton]
    calc x * (((List.range m).map fun k => (s ^ k) d₁).prod * (s ^ m) d₁)
        = (x * ((List.range m).map fun k => (s ^ k) d₁).prod) * (s ^ m) d₁ := by ring
      _ = ((List.range m).map fun k => (s ^ k) d₀).prod * ((s ^ m) x * (s ^ m) d₁) := by rw [ih]; ring
      _ = ((List.range m).map fun k => (s ^ k) d₀).prod * (s ^ m) (d₀ * s x) := by rw [← map_mul, h]
      _ = ((List.range m).map fun k => (s ^ k) d₀).prod * (s ^ m) d₀ * (s ^ (m + 1)) x := by
          rw [map_mul, pow_succ, RingHom.coe_mul, Function.comp_apply]; ring

theorem diag_list_prod {R : Type*} [CommRing R] (l : List (GL (Fin 2) R))
    (h : ∀ g ∈ l, ((g : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R) 0 1 = 0 ∧
      ((g : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R) 1 0 = 0) :
    ((l.prod : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R) 0 1 = 0 ∧
    ((l.prod : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R) 1 0 = 0 ∧
    ((l.prod : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R) 0 0 =
      (l.map fun g => ((g : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R) 0 0).prod ∧
    ((l.prod : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R) 1 1 =
      (l.map fun g => ((g : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R) 1 1).prod := by
  induction l with
  | nil =>
    simp only [List.prod_nil, List.map_nil, Units.val_one]
    exact ⟨Matrix.one_apply_ne (by decide), Matrix.one_apply_ne (by decide), Matrix.one_apply_eq 0, Matrix.one_apply_eq 1⟩
  | cons g l ih =>
    obtain ⟨h01, h10⟩ := h g List.mem_cons_self
    obtain ⟨i01, i10, i00, i11⟩ := ih fun g' hg' => h g' (List.mem_cons_of_mem _ hg')
    refine ⟨?_, ?_, ?_, ?_⟩ <;>
      simp [List.prod_cons, List.map_cons, Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two,
        h01, h10, i01, i10, i00, i11]

theorem normString_diag (K L : Type) [Field K] [Field L] [Algebra K L] (A : Type) [CommRing A] [Algebra K A]
    (τ : L ≃ₐ[K] L) (g : GL (Fin 2) (L ⊗[K] A))
    (h01 : ((g : GL (Fin 2) (L ⊗[K] A)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) 0 1 = 0)
    (h10 : ((g : GL (Fin 2) (L ⊗[K] A)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) 1 0 = 0) :
    ((normString K L A τ g : GL (Fin 2) (L ⊗[K] A)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) 0 1 = 0 ∧
    ((normString K L A τ g : GL (Fin 2) (L ⊗[K] A)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) 1 0 = 0 ∧
    ((normString K L A τ g : GL (Fin 2) (L ⊗[K] A)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) 0 0 =
      ((List.range (Module.finrank K L)).map fun k =>
        ((sigmaTensor K L A τ) ^ k) (((g : GL (Fin 2) (L ⊗[K] A)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) 0 0)).prod ∧
    ((normString K L A τ g : GL (Fin 2) (L ⊗[K] A)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) 1 1 =
      ((List.range (Module.finrank K L)).map fun k =>
        ((sigmaTensor K L A τ) ^ k) (((g : GL (Fin 2) (L ⊗[K] A)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) 1 1)).prod := by
  unfold normString
  obtain ⟨a, b, c, d⟩ := diag_list_prod ((List.range (Module.finrank K L)).map fun i => (⇑(sigmaGL K L A τ))^[i] g)
    (by
      intro g' hg'
      obtain ⟨i, -, rfl⟩ := List.mem_map.mp hg'
      rw [val_iterate_sigmaGL, val_iterate_sigmaGL, h01, h10, map_zero]
      exact ⟨rfl, rfl⟩)
  refine ⟨a, b, ?_, ?_⟩
  · rw [c, List.map_map]
    congr 1
    apply List.map_congr_left
    intro i _
    exact val_iterate_sigmaGL K L A τ g i 0 0
  · rw [d, List.map_map]
    congr 1
    apply List.map_congr_left
    intro i _
    exact val_iterate_sigmaGL K L A τ g i 1 1

theorem tensorArch_normString (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (τ : L ≃ₐ[K] L) (g : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K)) :
    tensorArch K L (normString K L (AdeleRing (𝓞 K) K) τ g) =
      normString K L (InfiniteAdeleRing K) τ (tensorArch K L g) := by
  unfold normString
  rw [map_list_prod, List.map_map]
  congr 1
  apply List.map_congr_left
  intro i _
  exact Function.Semiconj.iterate_right (tensorArch_sigmaGL K L τ) i g

theorem disc_map {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (g : GL (Fin 2) R) :
    Matrix.trace ((Matrix.GeneralLinearGroup.map f g : GL (Fin 2) S) : Matrix (Fin 2) (Fin 2) S) ^ 2 -
        4 * Matrix.det ((Matrix.GeneralLinearGroup.map f g : GL (Fin 2) S) : Matrix (Fin 2) (Fin 2) S) =
      f (Matrix.trace (g : Matrix (Fin 2) (Fin 2) R) ^ 2 - 4 * Matrix.det (g : Matrix (Fin 2) (Fin 2) R)) := by
  have hval : ((Matrix.GeneralLinearGroup.map f g : GL (Fin 2) S) : Matrix (Fin 2) (Fin 2) S) =
      (g : Matrix (Fin 2) (Fin 2) R).map f := rfl
  rw [hval, map_sub, map_mul, map_pow, map_ofNat, AddMonoidHom.map_trace, RingHom.map_det]
  rfl

theorem twistedCentralizer_diag (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] (τ : L ≃ₐ[K] L)
    (δ : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K))
    (hδ10 : (δ : Matrix (Fin 2) (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K)) 1 0 = 0)
    (hδ01 : (δ : Matrix (Fin 2) (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K)) 0 1 = 0)
    (hδ : IsRegularSemisimple (normString K L (AdeleRing (𝓞 K) K) τ δ))
    (t : twistedCentralizer K L (InfiniteAdeleRing K) τ (tensorArch K L δ)) :
    ((t : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) 0 1 = 0 ∧
    ((t : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) 1 0 = 0 := by

  set D : Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K) :=
    ((tensorArch K L δ : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) with hD
  set T : Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K) :=
    ((t : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) with hT
  set s : L ⊗[K] InfiniteAdeleRing K →+* L ⊗[K] InfiniteAdeleRing K := sigmaTensor K L (InfiniteAdeleRing K) τ with hs
  have hD01 : D 0 1 = 0 := by rw [hD, tensorArch_apply, hδ01, map_zero]
  have hD10 : D 1 0 = 0 := by rw [hD, tensorArch_apply, hδ10, map_zero]

  have hrel : T * D = D * ((sigmaGL K L (InfiniteAdeleRing K) τ (t : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) :
      GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) := by
    have h := (mem_sigmaCentralizer_iff.mp t.2)
    rw [mul_inv_eq_iff_eq_mul] at h
    rw [hT, hD, ← Units.val_mul, ← Units.val_mul, h]
  have hS : ∀ j k : Fin 2, ((sigmaGL K L (InfiniteAdeleRing K) τ (t : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) :
      GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) j k = s (T j k) :=
    fun _ _ => rfl
  have e01 : T 0 1 * D 1 1 = D 0 0 * s (T 0 1) := by
    have h := congrFun (congrFun hrel 0) 1
    simp only [Matrix.mul_apply, Fin.sum_univ_two, hD01, hD10, hS, mul_zero, zero_mul, add_zero, zero_add] at h
    exact h
  have e10 : T 1 0 * D 0 0 = D 1 1 * s (T 1 0) := by
    have h := congrFun (congrFun hrel 1) 0
    simp only [Matrix.mul_apply, Fin.sum_univ_two, hD01, hD10, hS, mul_zero, zero_mul, add_zero, zero_add] at h
    exact h

  obtain ⟨-, -, hN00, hN11⟩ := normString_diag K L (InfiniteAdeleRing K) τ (tensorArch K L δ) hD01 hD10
  have hreg : IsRegularSemisimple (normString K L (InfiniteAdeleRing K) τ (tensorArch K L δ)) := by
    rw [← tensorArch_normString]
    unfold IsRegularSemisimple
    unfold tensorArch
    rw [disc_map]
    exact hδ.map _
  obtain ⟨hN01, hN10, -, -⟩ := normString_diag K L (InfiniteAdeleRing K) τ (tensorArch K L δ) hD01 hD10
  have hu : IsUnit
      (((List.range (Module.finrank K L)).map fun k => (s ^ k) (D 0 0)).prod -
        ((List.range (Module.finrank K L)).map fun k => (s ^ k) (D 1 1)).prod) := by
    unfold IsRegularSemisimple at hreg
    rw [Matrix.trace_fin_two, Matrix.det_fin_two, hN01, hN10, hN00, hN11] at hreg
    have key : ∀ a b : L ⊗[K] InfiniteAdeleRing K, (a + b) ^ 2 - 4 * (a * b - 0 * 0) = (a - b) ^ 2 := fun a b => by ring
    rw [key] at hreg
    exact (isUnit_pow_iff two_ne_zero).mp hreg

  have t01 := telescope s (T 0 1) (D 0 0) (D 1 1) e01 (Module.finrank K L)
  have t10 := telescope s (T 1 0) (D 1 1) (D 0 0) e10 (Module.finrank K L)
  rw [hs, sigmaTensor_pow_finrank_apply] at t01 t10
  rw [hs] at hu
  constructor
  · refine (hu.mul_right_eq_zero).mp ?_
    rw [sub_mul, ← t01, mul_comm (T 0 1) _, sub_self]
  · refine (hu.mul_right_eq_zero).mp ?_
    rw [sub_mul, ← t10, mul_comm (T 1 0) _, sub_self]

end ArchWeightDiagL

open ArchWeightDiagL AutomorphicForm.WindowedSiegel in
theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] :
    (∀ t x : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K),
      (t : Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) 0 1 = 0 →
      (t : Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) 1 0 = 0 →
        (fun y : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K) =>
          -Real.log (AutomorphicForm.WindowedSiegel.archHeight L (AutomorphicForm.archIdentGL K L y))
            - Real.log (AutomorphicForm.WindowedSiegel.archHeight L
                (AdelicLevel.glArch (𝓞 L) L (AutomorphicForm.adelicWeyl (𝓞 L) L) *
                  AutomorphicForm.archIdentGL K L y))) (t * x) =
        (fun y : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K) =>
          -Real.log (AutomorphicForm.WindowedSiegel.archHeight L (AutomorphicForm.archIdentGL K L y))
            - Real.log (AutomorphicForm.WindowedSiegel.archHeight L
                (AdelicLevel.glArch (𝓞 L) L (AutomorphicForm.adelicWeyl (𝓞 L) L) *
                  AutomorphicForm.archIdentGL K L y))) x) ∧
    Continuous (fun y : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K) =>
          -Real.log (AutomorphicForm.WindowedSiegel.archHeight L (AutomorphicForm.archIdentGL K L y))
            - Real.log (AutomorphicForm.WindowedSiegel.archHeight L
                (AdelicLevel.glArch (𝓞 L) L (AutomorphicForm.adelicWeyl (𝓞 L) L) *
                  AutomorphicForm.archIdentGL K L y))) := by
  set Wl := AdelicLevel.glArch (𝓞 L) L (AutomorphicForm.adelicWeyl (𝓞 L) L) with hWdef
  have hW : ∀ v : NumberField.InfinitePlace L,
      ((NumberField.AdelicLevel.archComponent L v Wl : GL (Fin 2) v.Completion) : Matrix (Fin 2) (Fin 2) v.Completion) =
        !![0, 1; 1, 0] := fun v => by rw [hWdef]; exact val_archComponent_adelicWeyl L v

  have hHc : Continuous (AutomorphicForm.WindowedSiegel.archHeight L) := by
    unfold AutomorphicForm.WindowedSiegel.archHeight
    exact continuous_finsetProd _ fun v _ =>
      (continuous_localHeight'.comp (NumberField.AdelicLevel.continuous_archComponent L v)).pow _
  have hAc : Continuous (AutomorphicForm.archIdentGL K L) := map_continuous (AutomorphicForm.archIdentGLEquiv K L)
  have hcont : Continuous (fun y : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K) =>
      -Real.log (AutomorphicForm.WindowedSiegel.archHeight L (AutomorphicForm.archIdentGL K L y))
        - Real.log (AutomorphicForm.WindowedSiegel.archHeight L (Wl * AutomorphicForm.archIdentGL K L y))) :=
    (((hHc.comp hAc).log fun y => (archHeight_pos L _).ne').neg).sub
      ((hHc.comp ((continuous_const.mul continuous_id).comp hAc)).log fun y => (archHeight_pos L _).ne')
  refine ⟨?_, hcont⟩
  intro t x ht01 ht10
  have hg01 : ((AutomorphicForm.archIdentGL K L t : GL (Fin 2) (InfiniteAdeleRing L)) :
      Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing L)) 0 1 = 0 := by
    change AutomorphicForm.archIdent K L ((t : Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) 0 1) = 0
    rw [ht01, map_zero]
  have hg10 : ((AutomorphicForm.archIdentGL K L t : GL (Fin 2) (InfiniteAdeleRing L)) :
      Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing L)) 1 0 = 0 := by
    change AutomorphicForm.archIdent K L ((t : Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) 1 0) = 0
    rw [ht10, map_zero]
  have key : ∀ y : GL (Fin 2) (InfiniteAdeleRing L),
      AutomorphicForm.WindowedSiegel.archHeight L (AutomorphicForm.archIdentGL K L t * y) *
        AutomorphicForm.WindowedSiegel.archHeight L (Wl * (AutomorphicForm.archIdentGL K L t * y)) =
      AutomorphicForm.WindowedSiegel.archHeight L y * AutomorphicForm.WindowedSiegel.archHeight L (Wl * y) := by
    intro y
    unfold AutomorphicForm.WindowedSiegel.archHeight
    rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun v _ => ?_
    rw [← mul_pow, ← mul_pow]
    congr 1
    rw [map_mul, map_mul, map_mul, map_mul]
    exact localHeight_diag_mul_mul_localHeight_swap_mul _ _ _ (hW v)
      (by rw [NumberField.AdelicLevel.archComponent_apply, hg01]; rfl)
      (by rw [NumberField.AdelicLevel.archComponent_apply, hg10]; rfl)
  have hlog : ∀ y : GL (Fin 2) (InfiniteAdeleRing L),
      -Real.log (AutomorphicForm.WindowedSiegel.archHeight L y)
        - Real.log (AutomorphicForm.WindowedSiegel.archHeight L (Wl * y)) =
      -Real.log (AutomorphicForm.WindowedSiegel.archHeight L y *
        AutomorphicForm.WindowedSiegel.archHeight L (Wl * y)) := fun y => by
    rw [Real.log_mul (archHeight_pos L _).ne' (archHeight_pos L _).ne']
    ring
  show -Real.log _ - Real.log _ = -Real.log _ - Real.log _
  rw [map_mul, hlog, hlog, key]

end S_AutomorphicForm_archWeight_archIdentGL_diagonal_mul_and_continuous
end P2MW
export P2MW.S_AutomorphicForm_archWeight_archIdentGL_diagonal_mul_and_continuous (solution)
