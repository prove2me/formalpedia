-- Prove2me | solution 1 for AutomorphicForm.absNorm_sq_mul_relIndex_sq_mul_norm_det_trace_eq_norm_sixteen_mul_relIndex_sq_of_forall_isUnit
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/c51d593d-d89b-5c5d-8bb3-a9dc93c02c91

import Definitions.Def_AutomorphicForm_TwistedCommutant
import Definitions.Def_AutomorphicForm_BaseChangePlaces
import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_NumberField_TateGlobalZeta
import Theorems.Thm_IsDedekindDomain_HeightOneSpectrum_relIndex_span_range_mul_norm_det_eq_one_of_forall_mem_span
import Theorems.Thm_AutomorphicForm_exists_homeomorph_twistedCommutant_map_mul_scalar_forall_coe_eq_sum_map_tmul_of_linearIndependent
import Theorems.Thm_AutomorphicForm_exists_closure_iff_det_mem_integers_and_norm_det_trace_mul_absNorm_sq_eq_norm_sixteen_of_forall_isUnit
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_absNorm_sq_mul_relIndex_sq_mul_norm_det_trace_eq_norm_sixteen_mul_relIndex_sq_of_forall_isUnit

set_option autoImplicit false

open NumberField IsDedekindDomain AutomorphicForm
open scoped TensorProduct TensorProduct.RightActions

noncomputable section

namespace P2mE8Last2

section Gram

variable (K L : Type) [Field K] [Field L] [Algebra K L]
variable (A : Type) [CommRing A] [Algebra K A]

def trBil : L →ₗ[K] A →ₗ[K] A :=
  LinearMap.mk₂ K (fun l a => Algebra.trace K L l • a)
    (fun l₁ l₂ a => by simp only [map_add, add_smul])
    (fun c l a => by simp only [map_smul, smul_assoc])
    (fun l a₁ a₂ => by simp only [smul_add])
    (fun c l a => by
      show Algebra.trace K L l • (c • a) = c • (Algebra.trace K L l • a)
      exact smul_comm _ _ _)

def trF : L ⊗[K] A →ₗ[A] A where
  toFun := TensorProduct.lift (trBil K L A)
  map_add' := fun z w => map_add _ z w
  map_smul' := by
    intro c z
    induction z using TensorProduct.induction_on with
    | zero => rw [smul_zero, map_zero, smul_zero]
    | tmul l a =>
        rw [rightActions_smul_eq K L A c, Algebra.TensorProduct.tmul_mul_tmul, one_mul, TensorProduct.lift.tmul,
          TensorProduct.lift.tmul]
        show Algebra.trace K L l • (c * a) = c • (Algebra.trace K L l • a)
        rw [smul_eq_mul, Algebra.smul_def, Algebra.smul_def]
        ring
    | add z w hz hw => rw [smul_add, map_add, hz, hw, map_add, smul_add]

theorem trF_tmul (l : L) (a : A) : trF K L A (l ⊗ₜ[K] a) = Algebra.trace K L l • a :=
  TensorProduct.lift.tmul l a

def gram {ι : Type} (u : ι → Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) : Matrix ι ι A :=
  Matrix.of fun i j => trF K L A (Matrix.trace (u i * u j))

def bf (X Y : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) : A := trF K L A (Matrix.trace (X * Y))

theorem gram_apply {ι : Type} (u : ι → Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) (i j : ι) :
    gram K L A u i j = bf K L A (u i) (u j) := rfl

theorem bf_add_left (X X' Y : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) :
    bf K L A (X + X') Y = bf K L A X Y + bf K L A X' Y := by
  unfold bf; rw [add_mul, Matrix.trace_add, map_add]

theorem bf_add_right (X Y Y' : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) :
    bf K L A X (Y + Y') = bf K L A X Y + bf K L A X Y' := by
  unfold bf; rw [mul_add, Matrix.trace_add, map_add]

theorem bf_smul_left (c : A) (X Y : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) :
    bf K L A (c • X) Y = c * bf K L A X Y := by
  unfold bf; rw [Matrix.smul_mul, Matrix.trace_smul, map_smul, smul_eq_mul]

theorem bf_smul_right (c : A) (X Y : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) :
    bf K L A X (c • Y) = c * bf K L A X Y := by
  unfold bf; rw [Matrix.mul_smul, Matrix.trace_smul, map_smul, smul_eq_mul]

theorem bf_zero_left (Y : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) : bf K L A 0 Y = 0 := by
  unfold bf; rw [zero_mul, Matrix.trace_zero, map_zero]

theorem bf_zero_right (X : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) : bf K L A X 0 = 0 := by
  unfold bf; rw [mul_zero, Matrix.trace_zero, map_zero]

theorem bf_sum_left {ι : Type} (s : Finset ι) (X : ι → Matrix (Fin 2) (Fin 2) (L ⊗[K] A))
    (Y : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) :
    bf K L A (∑ i ∈ s, X i) Y = ∑ i ∈ s, bf K L A (X i) Y := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty, Finset.sum_empty, bf_zero_left]
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, bf_add_left, ih]

theorem bf_sum_right {ι : Type} (s : Finset ι) (X : Matrix (Fin 2) (Fin 2) (L ⊗[K] A))
    (Y : ι → Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) :
    bf K L A X (∑ i ∈ s, Y i) = ∑ i ∈ s, bf K L A X (Y i) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty, Finset.sum_empty, bf_zero_right]
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, bf_add_right, ih]

theorem gram_linComb {ι : Type} [Fintype ι] (u : ι → Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) (P : Matrix ι ι A) :
    gram K L A (fun k => ∑ i, P i k • u i) = P.transpose * gram K L A u * P := by
  ext k l
  rw [gram_apply, Matrix.mul_apply]
  simp only [Matrix.mul_apply, Matrix.transpose_apply, gram_apply]
  rw [bf_sum_left]
  simp only [bf_smul_left, bf_sum_right, bf_smul_right, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
  ring

theorem det_gram_linComb {ι : Type} [Fintype ι] [DecidableEq ι] (u : ι → Matrix (Fin 2) (Fin 2) (L ⊗[K] A))
    (P : Matrix ι ι A) :
    (gram K L A (fun k => ∑ i, P i k • u i)).det = P.det ^ 2 * (gram K L A u).det := by
  rw [gram_linComb, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose]
  ring

theorem gram_map_includeLeft {ι : Type} (x : ι → Matrix (Fin 2) (Fin 2) L) :
    gram K L A (fun i => (x i).map (fun l : L => l ⊗ₜ[K] (1 : A))) =
      (Matrix.of fun i j : ι => Algebra.trace K L (Matrix.trace (x i * x j))).map (algebraMap K A) := by
  ext i j
  rw [gram_apply, Matrix.map_apply, Matrix.of_apply, bf]
  have hmap : ∀ M : Matrix (Fin 2) (Fin 2) L, M.map (fun l : L => l ⊗ₜ[K] (1 : A)) =
      M.map ⇑(Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] A) := fun M => rfl
  rw [hmap, hmap, ← Matrix.map_mul, ← AddMonoidHom.map_trace]
  show trF K L A (Matrix.trace (x i * x j) ⊗ₜ[K] (1 : A)) = _
  rw [trF_tmul, Algebra.algebraMap_eq_smul_one]

theorem gram_mulVec {ι : Type} [Fintype ι] (u : ι → Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) (c : ι → A) (i : ι) :
    (gram K L A u).mulVec c i = bf K L A (u i) (∑ k, c k • u k) := by
  rw [Matrix.mulVec, bf_sum_right]
  simp only [dotProduct, gram_apply, bf_smul_right]
  refine Finset.sum_congr rfl fun k _ => ?_
  ring

theorem linearIndependent_of_det_gram_ne_zero [IsDomain A] {ι : Type} [Fintype ι] [DecidableEq ι]
    (u : ι → Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) (h : (gram K L A u).det ≠ 0) : LinearIndependent A u := by
  rw [Fintype.linearIndependent_iff]
  intro c hc
  by_contra hne
  push_neg at hne
  obtain ⟨i, hi⟩ := hne
  apply h
  rw [← Matrix.exists_mulVec_eq_zero_iff]
  refine ⟨c, fun h0 => hi (by rw [h0]; rfl), ?_⟩
  funext j
  rw [gram_mulVec, hc, bf_zero_right]
  rfl

theorem gram_reindex {ι ι' : Type} (e : ι' ≃ ι) (u : ι → Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) :
    gram K L A (u ∘ e) = (gram K L A u).submatrix e e := rfl

end Gram

section Lattice

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
variable (v : HeightOneSpectrum (𝓞 K))

theorem map_tmul_eq_smul (X : Matrix (Fin 2) (Fin 2) L) (a : v.adicCompletion K) :
    X.map (fun l : L => l ⊗ₜ[K] a) = a • X.map (fun l : L => l ⊗ₜ[K] (1 : v.adicCompletion K)) := by
  ext i j
  simp only [Matrix.map_apply, Matrix.smul_apply]
  rw [rightActions_smul_eq K L (v.adicCompletion K) a, Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]

theorem closure_eq_span_toAddSubgroup {M : Type} [AddCommGroup M] [Module (v.adicCompletion K) M]
    (T : Set M) (S : Set M) (hST : S ⊆ T)
    (hT : T ⊆ (Submodule.span (v.adicCompletionIntegers K) S : Set M))
    (hstab : ∀ (r : v.adicCompletionIntegers K), ∀ X ∈ T, r • X ∈ T) :
    AddSubgroup.closure T = (Submodule.span (v.adicCompletionIntegers K) S).toAddSubgroup := by
  refine le_antisymm ((AddSubgroup.closure_le _).2 hT) ?_
  intro X hX
  rw [Submodule.mem_toAddSubgroup] at hX
  induction hX using Submodule.span_induction with
  | mem X hX => exact AddSubgroup.subset_closure (hST hX)
  | zero => exact zero_mem _
  | add X Y _ _ hX hY => exact add_mem hX hY
  | smul r X hXs hX =>
      clear hXs
      induction hX using AddSubgroup.closure_induction with
      | mem Y hY => exact AddSubgroup.subset_closure (hstab r Y hY)
      | zero => rw [smul_zero]; exact zero_mem _
      | add Y Z _ _ hY hZ => rw [smul_add]; exact add_mem hY hZ
      | neg Y _ hY => rw [smul_neg]; exact neg_mem hY

theorem closure_setΛ_eq {κ : Type} (x : κ → Matrix (Fin 2) (Fin 2) L) :
    AddSubgroup.closure
        {X : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K) |
          ∃ (i : κ) (a : v.adicCompletion K), a ∈ v.adicCompletionIntegers K ∧
            X = (x i).map (fun l : L => l ⊗ₜ[K] a)} =
      (Submodule.span (v.adicCompletionIntegers K)
        (Set.range fun i => (x i).map (fun l : L => l ⊗ₜ[K] (1 : v.adicCompletion K)))).toAddSubgroup := by
  refine closure_eq_span_toAddSubgroup K v _ _ ?_ ?_ ?_
  · rintro X ⟨i, rfl⟩
    exact ⟨i, 1, one_mem _, rfl⟩
  · rintro X ⟨i, a, ha, rfl⟩
    rw [map_tmul_eq_smul, SetLike.mem_coe,
      show a • (x i).map (fun l : L => l ⊗ₜ[K] (1 : v.adicCompletion K)) =
        (⟨a, ha⟩ : v.adicCompletionIntegers K) • (x i).map (fun l : L => l ⊗ₜ[K] (1 : v.adicCompletion K)) from rfl]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  · rintro r X ⟨i, a, ha, rfl⟩
    refine ⟨i, (r : v.adicCompletion K) * a, mul_mem r.2 ha, ?_⟩
    rw [map_tmul_eq_smul, map_tmul_eq_smul K L v (x i) ((r : v.adicCompletion K) * a), mul_smul]
    rfl

theorem map_mulOne_eq_smul (X : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) (a : v.adicCompletion K) :
    X.map (fun t : L ⊗[K] v.adicCompletion K => t * ((1 : L) ⊗ₜ[K] a)) = a • X := by
  ext i j
  simp only [Matrix.map_apply, Matrix.smul_apply]
  rw [rightActions_smul_eq K L (v.adicCompletion K) a, mul_comm]

theorem closure_setF_eq {ι : Type} (f : ι → Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) :
    AddSubgroup.closure
        {X : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K) |
          ∃ (i : ι) (a : v.adicCompletion K), a ∈ v.adicCompletionIntegers K ∧
            X = (f i).map (fun t : L ⊗[K] v.adicCompletion K => t * ((1 : L) ⊗ₜ[K] a))} =
      (Submodule.span (v.adicCompletionIntegers K) (Set.range f)).toAddSubgroup := by
  refine closure_eq_span_toAddSubgroup K v _ _ ?_ ?_ ?_
  · rintro X ⟨i, rfl⟩
    refine ⟨i, 1, one_mem _, ?_⟩
    rw [map_mulOne_eq_smul, one_smul]
  · rintro X ⟨i, a, ha, rfl⟩
    rw [map_mulOne_eq_smul, SetLike.mem_coe,
      show a • f i = (⟨a, ha⟩ : v.adicCompletionIntegers K) • f i from rfl]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  · rintro r X ⟨i, a, ha, rfl⟩
    refine ⟨i, (r : v.adicCompletion K) * a, mul_mem r.2 ha, ?_⟩
    rw [map_mulOne_eq_smul, map_mulOne_eq_smul, mul_smul]
    rfl

set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 6400000 in

theorem span_range_coe_eq_map {W : Submodule (v.adicCompletion K) (Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K))}
    {κ : Type} (u : κ → W) :
    letI : Module (v.adicCompletionIntegers K) W := Submodule.module' W
    (Submodule.span (v.adicCompletionIntegers K)
        (Set.range fun k => (u k : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)))).toAddSubgroup =
      (Submodule.span (v.adicCompletionIntegers K) (Set.range u)).toAddSubgroup.map
        W.subtype.toAddMonoidHom := by
  letI : Module (v.adicCompletionIntegers K) W := Submodule.module' W
  haveI : IsScalarTower (v.adicCompletionIntegers K) (v.adicCompletion K) W := Submodule.isScalarTower W
  have h : Submodule.span (v.adicCompletionIntegers K)
        (Set.range fun k => (u k : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K))) =
      (Submodule.span (v.adicCompletionIntegers K) (Set.range u)).map
        (W.subtype.restrictScalars (v.adicCompletionIntegers K)) := by
    rw [Submodule.map_span, ← Set.range_comp]
    rfl
  rw [h]
  ext X
  simp only [Submodule.mem_toAddSubgroup, Submodule.mem_map, AddSubgroup.mem_map]
  constructor
  · rintro ⟨w, hw, rfl⟩; exact ⟨w, hw, rfl⟩
  · rintro ⟨w, hw, rfl⟩; exact ⟨w, hw, rfl⟩

end Lattice

section Main

set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 12800000 in
theorem main
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (h2 : Module.finrank K L = 2) (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (δ₀ : GL (Fin 2) L)
    {κ : Type} [Fintype κ] [DecidableEq κ] (hκ : Fintype.card κ = 4)
    (x : κ → Matrix (Fin 2) (Fin 2) L) (hx : LinearIndependent K x)
    (hspan : ∀ X : Matrix (Fin 2) (Fin 2) L,
      X * (δ₀ : Matrix (Fin 2) (Fin 2) L) = (δ₀ : Matrix (Fin 2) (Fin 2) L) * X.map σ ↔
        X ∈ Submodule.span K (Set.range x))
    (v : HeightOneSpectrum (𝓞 K))
    (hdiv : ∀ X ∈ twistedCommutant K L (v.adicCompletion K) σ
        (Matrix.GeneralLinearGroup.map
          (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] v.adicCompletion K) δ₀),
      X ≠ 0 → IsUnit X) :
    let SΛ : AddSubgroup (Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) :=
      AddSubgroup.closure
        {X : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K) |
          ∃ (i : κ) (a : v.adicCompletion K), a ∈ v.adicCompletionIntegers K ∧
            X = (x i).map (fun l : L => l ⊗ₜ[K] a)}
    let SM : AddSubgroup (Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) :=
      AddSubgroup.closure
        {X : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K) |
          X ∈ twistedCommutant K L (v.adicCompletion K) σ
              (Matrix.GeneralLinearGroup.map
                (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] v.adicCompletion K) δ₀) ∧
            ∃ a : v.adicCompletion K, a ∈ v.adicCompletionIntegers K ∧ X.det = (1 : L) ⊗ₜ[K] a}
    ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ 2 * (SΛ.relIndex SM : ℝ) ^ 2 *
        ‖algebraMap K (v.adicCompletion K)
          (Matrix.of fun i j : κ => Algebra.trace K L (Matrix.trace (x i * x j))).det‖ =
      ‖(16 : v.adicCompletion K)‖ * (SM.relIndex SΛ : ℝ) ^ 2 := by
  intro SΛ SM

  set F := v.adicCompletion K with hF
  set O := v.adicCompletionIntegers K with hO
  set δ : GL (Fin 2) (L ⊗[K] F) :=
    Matrix.GeneralLinearGroup.map (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] F) δ₀ with hδdef
  set q : ℝ := ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) with hq

  set bx : κ → Matrix (Fin 2) (Fin 2) (L ⊗[K] F) := fun i => (x i).map (fun l : L => l ⊗ₜ[K] (1 : F)) with hbx
  haveI : Nonempty κ := by
    rw [← Fintype.card_pos_iff, hκ]; norm_num
  obtain ⟨eκ⟩ : Nonempty (κ ≃ Fin 4) := ⟨Fintype.equivOfCardEq (by rw [hκ, Fintype.card_fin])⟩

  obtain ⟨e, he⟩ :=
    AutomorphicForm.exists_homeomorph_twistedCommutant_map_mul_scalar_forall_coe_eq_sum_map_tmul_of_linearIndependent
      K L F σ δ₀ 1 κ x hx hspan
  have hδ : Matrix.GeneralLinearGroup.map
        (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] F) δ₀ *
      Matrix.GeneralLinearGroup.scalar (Fin 2) (1 : (L ⊗[K] F)ˣ) = δ := by
    rw [map_one, mul_one]
  have hsum : ∀ a : κ → F, ∑ i, (x i).map (fun l : L => l ⊗ₜ[K] a i) = ∑ i, a i • bx i := fun a =>
    Finset.sum_congr rfl fun i _ => map_tmul_eq_smul K L v (x i) (a i)
  have hmemW : ∀ X ∈ twistedCommutant K L F σ δ, X ∈ Submodule.span F (Set.range bx) := by
    intro X hX
    rw [← hδ] at hX
    have hXe : X = ((e (e.symm ⟨X, hX⟩) : twistedCommutant K L F σ _) : Matrix (Fin 2) (Fin 2) (L ⊗[K] F)) := by
      rw [Homeomorph.apply_symm_apply]
    rw [hXe, he, hsum]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  have hrepr : ∀ X ∈ twistedCommutant K L F σ δ, ∃ a : κ → F, X = ∑ i, a i • bx i := by
    intro X hX
    rw [← hδ] at hX
    refine ⟨e.symm ⟨X, hX⟩, ?_⟩
    rw [← hsum, ← he, Homeomorph.apply_symm_apply]
  have hli : LinearIndependent F bx := by
    rw [Fintype.linearIndependent_iff]
    intro a ha
    have h0 : e a = e 0 := by
      apply Subtype.ext
      rw [he, he, hsum, hsum, ha]
      simp
    have := e.injective h0
    exact fun i => congrFun this i
  have hbxD : ∀ i, bx i ∈ twistedCommutant K L F σ δ := by
    intro i
    have hval : ((e (Pi.single i 1) : twistedCommutant K L F σ _) : Matrix (Fin 2) (Fin 2) (L ⊗[K] F)) = bx i := by
      rw [he, hsum, Finset.sum_eq_single i]
      · rw [Pi.single_eq_same, one_smul]
      · intro j _ hj
        rw [Pi.single_eq_of_ne hj, zero_smul]
      · intro h; exact absurd (Finset.mem_univ i) h
    have hmem : bx i ∈ twistedCommutant K L F σ (Matrix.GeneralLinearGroup.map
        (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] F) δ₀ *
      Matrix.GeneralLinearGroup.scalar (Fin 2) (1 : (L ⊗[K] F)ˣ)) := by
      rw [← hval]
      exact (e (Pi.single i 1)).2
    rwa [hδ] at hmem
  have hsmulD : ∀ (a : F) (X : Matrix (Fin 2) (Fin 2) (L ⊗[K] F)), X ∈ twistedCommutant K L F σ δ →
      a • X ∈ twistedCommutant K L F σ δ := by
    intro a X hX
    have h := includeRight_smul_mem_twistedCommutant (σ := σ) δ hX a
    have heq : (Algebra.TensorProduct.includeRight (R := K) (A := L) a) • X = a • X := by
      ext i j
      simp only [Matrix.smul_apply, smul_eq_mul, Algebra.TensorProduct.includeRight_apply]
      rw [rightActions_smul_eq K L F a]
    rw [heq] at h
    exact h
  set W : Submodule F (Matrix (Fin 2) (Fin 2) (L ⊗[K] F)) := Submodule.span F (Set.range bx) with hW
  letI instOW : Module O W := Submodule.module' W
  haveI instOFW : IsScalarTower O F W := Submodule.isScalarTower W
  let b₂ : Module.Basis κ F W := Module.Basis.span hli
  have hb₂ : ∀ i, (b₂ i : Matrix (Fin 2) (Fin 2) (L ⊗[K] F)) = bx i := fun i => by
    rw [Module.Basis.span_apply]

  set e4 : Fin 4 → Matrix (Fin 2) (Fin 2) (L ⊗[K] F) := bx ∘ eκ.symm with he4
  have hli4 : LinearIndependent F e4 := hli.comp _ eκ.symm.injective
  have hsum4 : ∀ a : Fin 4 → F,
      ∑ j, (e4 j).map (fun t : L ⊗[K] F => t * ((1 : L) ⊗ₜ[K] a j)) = ∑ j, a j • e4 j := fun a =>
    Finset.sum_congr rfl fun j _ => map_mulOne_eq_smul K L v (e4 j) (a j)
  have hbasis : ∀ X : Matrix (Fin 2) (Fin 2) (L ⊗[K] F),
      X ∈ twistedCommutant K L F σ δ ↔
        ∃! a : Fin 4 → F, X = ∑ j, (e4 j).map (fun t : L ⊗[K] F => t * ((1 : L) ⊗ₜ[K] a j)) := by
    intro X
    constructor
    · intro hX
      obtain ⟨a, rfl⟩ := hrepr X hX
      refine ⟨a ∘ eκ.symm, ?_, ?_⟩
      · show ∑ i, a i • bx i = ∑ j, (e4 j).map (fun t : L ⊗[K] F => t * ((1 : L) ⊗ₜ[K] (a ∘ eκ.symm) j))
        rw [hsum4]
        exact (Equiv.sum_comp eκ.symm (fun i => a i • bx i)).symm
      · intro a' ha'
        rw [hsum4] at ha'
        have hcomp : ∑ i, a i • bx i = ∑ j, (a ∘ eκ.symm) j • e4 j :=
          (Equiv.sum_comp eκ.symm (fun i => a i • bx i)).symm
        rw [hcomp] at ha'
        have hzero : ∑ j, (a' j - (a ∘ eκ.symm) j) • e4 j = 0 := by
          simp only [sub_smul, Finset.sum_sub_distrib]
          rw [← ha', sub_self]
        have := Fintype.linearIndependent_iff.1 hli4 _ hzero
        funext j
        exact sub_eq_zero.1 (this j)
    · rintro ⟨a, ha, -⟩
      rw [ha, hsum4]
      exact Subalgebra.sum_mem _ fun j _ => hsmulD _ _ (hbxD _)
  set τ : L ⊗[K] F →+ F := (trF K L F).toAddMonoidHom with hτdef
  have hτ : ∀ (l : L) (a : F), τ (l ⊗ₜ[K] a) = algebraMap K F (Algebra.trace K L l) * a := by
    intro l a
    show trF K L F (l ⊗ₜ[K] a) = _
    rw [trF_tmul, Algebra.smul_def]
  obtain ⟨f, hfiff, hfnorm⟩ :=
    AutomorphicForm.exists_closure_iff_det_mem_integers_and_norm_det_trace_mul_absNorm_sq_eq_norm_sixteen_of_forall_isUnit
      K L h2 σ hgen v δ e4 hbasis hdiv τ hτ
  have hgramf : (Matrix.of fun i j : Fin 4 => τ (Matrix.trace (f i * f j))) = gram K L F f := rfl
  rw [hgramf] at hfnorm

  have h16 : ‖(16 : F)‖ ≠ 0 := by
    rw [norm_ne_zero_iff, show (16 : F) = algebraMap K F 16 by norm_num [map_ofNat],
      map_ne_zero_iff _ (algebraMap K F).injective]
    norm_num
  have hdetf : (gram K L F f).det ≠ 0 := by
    intro h0
    apply h16
    rw [← hfnorm, h0, norm_zero, zero_mul]
  have hfD : ∀ k, f k ∈ twistedCommutant K L F σ δ := by
    intro k
    have hk : f k ∈ AddSubgroup.closure
        {X : Matrix (Fin 2) (Fin 2) (L ⊗[K] F) |
          ∃ (i : Fin 4) (a : F), a ∈ O ∧ X = (f i).map (fun t : L ⊗[K] F => t * ((1 : L) ⊗ₜ[K] a))} := by
      refine AddSubgroup.subset_closure ⟨k, 1, one_mem _, ?_⟩
      rw [map_mulOne_eq_smul, one_smul]
    exact ((hfiff (f k)).1 hk).1
  have hfW : ∀ k, f k ∈ W := fun k => hmemW _ (hfD k)
  have hlif : LinearIndependent F f := linearIndependent_of_det_gram_ne_zero K L F f hdetf
  set fκ : κ → Matrix (Fin 2) (Fin 2) (L ⊗[K] F) := f ∘ eκ with hfκ
  let fW : κ → W := fun k => ⟨fκ k, hfW (eκ k)⟩
  have hlifW : LinearIndependent F fW := by
    refine LinearIndependent.of_comp W.subtype ?_
    have : (⇑W.subtype ∘ fW) = fκ := rfl
    rw [this]
    exact hlif.comp _ eκ.injective
  have hcard : Fintype.card κ = Module.finrank F W := by
    rw [hW, finrank_span_eq_card hli]
  let b₁ : Module.Basis κ F W := basisOfLinearIndependentOfCardEqFinrank hlifW hcard
  have hb₁ : ∀ k, (b₁ k : Matrix (Fin 2) (Fin 2) (L ⊗[K] F)) = fκ k := fun k => by
    show ((basisOfLinearIndependentOfCardEqFinrank hlifW hcard : Module.Basis κ F W) k :
      Matrix (Fin 2) (Fin 2) (L ⊗[K] F)) = fκ k
    rw [coe_basisOfLinearIndependentOfCardEqFinrank]

  obtain ⟨d, hd⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors O)
    (fun ki : κ × κ => (b₂.repr (b₁ ki.1)) ki.2)
  set dF : F := ((d : O) : F) with hdF
  have hdF0 : dF ≠ 0 := by
    intro h
    apply nonZeroDivisors.coe_ne_zero d
    exact IsFractionRing.injective O F (by rw [map_zero]; exact h)
  choose o ho using hd
  let b₁' : Module.Basis κ F W := b₁.unitsSMul fun _ => Units.mk0 dF hdF0
  have hb₁' : ∀ k, b₁' k = dF • b₁ k := fun k => by
    show (b₁.unitsSMul fun _ => Units.mk0 dF hdF0) k = dF • b₁ k
    rw [Module.Basis.unitsSMul_apply, Units.smul_def, Units.val_mk0]
  have hb₁'fun : (⇑b₁' : κ → W) = fun k => dF • b₁ k := funext hb₁'
  have hnest₂ : ∀ k, b₁' k ∈ Submodule.span O (Set.range b₂) := by
    intro k
    rw [hb₁', ← b₂.sum_repr (b₁ k), Finset.smul_sum]
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [← mul_smul, show dF * (b₂.repr (b₁ k)) i = (d : O) • (b₂.repr (b₁ (k, i).1)) (k, i).2 from rfl, ← ho (k, i),
      show (algebraMap O F) (o (k, i)) • b₂ i = (o (k, i)) • b₂ i from rfl]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  have hnest₁ : ∀ k, b₁' k ∈ Submodule.span O (Set.range b₁) := by
    intro k
    rw [hb₁', show dF • b₁ k = (d : O) • b₁ k from rfl]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)

  have k3a := IsDedekindDomain.HeightOneSpectrum.relIndex_span_range_mul_norm_det_eq_one_of_forall_mem_span
    K v b₁' b₂ hnest₂
  have k3b := IsDedekindDomain.HeightOneSpectrum.relIndex_span_range_mul_norm_det_eq_one_of_forall_mem_span
    K v b₁' b₁ hnest₁
  have hdet₂ : b₂.det b₁' = dF ^ Fintype.card κ * b₂.det b₁ := by
    rw [hb₁'fun, AlternatingMap.map_smul_univ, Finset.prod_const, Finset.card_univ, smul_eq_mul]
  have hdet₁ : b₁.det b₁' = dF ^ Fintype.card κ := by
    rw [hb₁'fun, AlternatingMap.map_smul_univ, Finset.prod_const, Finset.card_univ, Module.Basis.det_self,
      smul_eq_mul, mul_one]
  rw [hdet₂, hκ] at k3a
  rw [hdet₁, hκ] at k3b

  set ΛM : AddSubgroup (Matrix (Fin 2) (Fin 2) (L ⊗[K] F)) :=
    (Submodule.span O (Set.range bx)).toAddSubgroup with hΛM
  set MM : AddSubgroup (Matrix (Fin 2) (Fin 2) (L ⊗[K] F)) :=
    (Submodule.span O (Set.range fκ)).toAddSubgroup with hMM
  set AM : AddSubgroup (Matrix (Fin 2) (Fin 2) (L ⊗[K] F)) :=
    (Submodule.span O (Set.range fun k => dF • fκ k)).toAddSubgroup with hAM
  have hinjW : Function.Injective W.subtype.toAddMonoidHom := Subtype.val_injective
  have hcoe₂ : (fun k => (b₂ k : Matrix (Fin 2) (Fin 2) (L ⊗[K] F))) = bx := funext hb₂
  have hcoe₁ : (fun k => (b₁ k : Matrix (Fin 2) (Fin 2) (L ⊗[K] F))) = fκ := funext hb₁
  have hcoe₁' : (fun k => (b₁' k : Matrix (Fin 2) (Fin 2) (L ⊗[K] F))) = fun k => dF • fκ k :=
    funext fun k => by rw [hb₁', Submodule.coe_smul, hb₁]
  have hΛM' : ΛM = (Submodule.span O (Set.range b₂)).toAddSubgroup.map W.subtype.toAddMonoidHom := by
    rw [hΛM, ← span_range_coe_eq_map, hcoe₂]
  have hMM' : MM = (Submodule.span O (Set.range b₁)).toAddSubgroup.map W.subtype.toAddMonoidHom := by
    rw [hMM, ← span_range_coe_eq_map, hcoe₁]
  have hAM' : AM = (Submodule.span O (Set.range b₁')).toAddSubgroup.map W.subtype.toAddMonoidHom := by
    rw [hAM, ← span_range_coe_eq_map, hcoe₁']
  have hIΛ : AM.relIndex ΛM = (Submodule.span O (Set.range b₁')).toAddSubgroup.relIndex
      (Submodule.span O (Set.range b₂)).toAddSubgroup := by
    rw [hAM', hΛM', AddSubgroup.relIndex_map_map_of_injective _ _ hinjW]
  have hIM : AM.relIndex MM = (Submodule.span O (Set.range b₁')).toAddSubgroup.relIndex
      (Submodule.span O (Set.range b₁)).toAddSubgroup := by
    rw [hAM', hMM', AddSubgroup.relIndex_map_map_of_injective _ _ hinjW]
  rw [← hIΛ] at k3a
  rw [← hIM] at k3b

  have hSΛ : SΛ = ΛM := closure_setΛ_eq K L v x
  have hSM : SM = MM := by
    have hset : {X : Matrix (Fin 2) (Fin 2) (L ⊗[K] F) |
          X ∈ twistedCommutant K L F σ δ ∧ ∃ a : F, a ∈ O ∧ X.det = (1 : L) ⊗ₜ[K] a} =
        (AddSubgroup.closure
          {X : Matrix (Fin 2) (Fin 2) (L ⊗[K] F) |
            ∃ (i : Fin 4) (a : F), a ∈ O ∧ X = (f i).map (fun t : L ⊗[K] F => t * ((1 : L) ⊗ₜ[K] a))} :
          Set (Matrix (Fin 2) (Fin 2) (L ⊗[K] F))) := by
      ext X
      rw [Set.mem_setOf_eq, SetLike.mem_coe]
      exact (hfiff X).symm
    show AddSubgroup.closure {X : Matrix (Fin 2) (Fin 2) (L ⊗[K] F) |
          X ∈ twistedCommutant K L F σ δ ∧ ∃ a : F, a ∈ O ∧ X.det = (1 : L) ⊗ₜ[K] a} = MM
    rw [hset, AddSubgroup.closure_eq, closure_setF_eq K L v f, hMM, hfκ, eκ.surjective.range_comp]
  rw [hSΛ, hSM]

  have hAM_le_MM : AM ≤ MM := by
    rw [hAM, hMM]
    refine Submodule.toAddSubgroup_mono (Submodule.span_le.2 ?_)
    rintro X ⟨k, rfl⟩
    show dF • fκ k ∈ (Submodule.span O (Set.range fκ) : Set (Matrix (Fin 2) (Fin 2) (L ⊗[K] F)))
    rw [SetLike.mem_coe, show dF • fκ k = (d : O) • fκ k from rfl]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
  have hAM_le_ΛM : AM ≤ ΛM := by
    rw [hAM', hΛM']
    refine AddSubgroup.map_mono (Submodule.toAddSubgroup_mono (Submodule.span_le.2 ?_))
    rintro X ⟨k, rfl⟩
    exact hnest₂ k
  set t : ℕ := AM.relIndex (MM ⊓ ΛM) with ht
  have e1 : AM.relIndex MM = t * ΛM.relIndex MM := by
    rw [ht, ← AddSubgroup.relIndex_mul_relIndex AM (MM ⊓ ΛM) MM (le_inf hAM_le_MM hAM_le_ΛM) inf_le_left,
      inf_comm, AddSubgroup.inf_relIndex_right, inf_comm]
  have e2 : AM.relIndex ΛM = t * MM.relIndex ΛM := by
    rw [ht, ← AddSubgroup.relIndex_mul_relIndex AM (MM ⊓ ΛM) ΛM (le_inf hAM_le_MM hAM_le_ΛM) inf_le_right,
      AddSubgroup.inf_relIndex_right]
  rw [e2, Nat.cast_mul] at k3a
  rw [e1, Nat.cast_mul] at k3b

  have hlin : (fun k => ∑ i, (b₂.toMatrix b₁) i k • bx i) = fκ := by
    funext k
    have := congrArg (fun w : W => (w : Matrix (Fin 2) (Fin 2) (L ⊗[K] F))) (b₂.sum_repr (b₁ k))
    simp only [Submodule.coe_sum, Submodule.coe_smul] at this
    rw [hb₁] at this
    rw [← this]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Module.Basis.toMatrix_apply, hb₂]
  have hdetP : (b₂.toMatrix b₁).det = b₂.det b₁ := (Module.Basis.det_apply b₂ b₁).symm
  have hgram₁ : (gram K L F fκ).det = (b₂.det b₁) ^ 2 *
      algebraMap K F (Matrix.of fun i j : κ => Algebra.trace K L (Matrix.trace (x i * x j))).det := by
    rw [← hlin, det_gram_linComb, hdetP, hbx, gram_map_includeLeft, RingHom.map_det, RingHom.mapMatrix_apply]
  have hgram₂ : ‖(gram K L F fκ).det‖ * q ^ 2 = ‖(16 : F)‖ := by
    rw [hfκ, gram_reindex, Matrix.det_submatrix_equiv_self]
    exact hfnorm
  have hgram : ‖algebraMap K F (Matrix.of fun i j : κ => Algebra.trace K L (Matrix.trace (x i * x j))).det‖ *
      ‖b₂.det b₁‖ ^ 2 * q ^ 2 = ‖(16 : F)‖ := by
    rw [← hgram₂, hgram₁, norm_mul, norm_pow]
    ring

  set a : ℝ := (ΛM.relIndex MM : ℝ) with ha
  set b : ℝ := (MM.relIndex ΛM : ℝ) with hb
  set T : ℝ := (t : ℝ) with hT
  set P : ℝ := ‖b₂.det b₁‖ with hP
  set g : ℝ := ‖algebraMap K F (Matrix.of fun i j : κ => Algebra.trace K L (Matrix.trace (x i * x j))).det‖ with hg
  have hD : ‖dF ^ 4 * b₂.det b₁‖ = ‖dF‖ ^ 4 * P := by rw [norm_mul, norm_pow]
  rw [hD] at k3a
  rw [norm_pow] at k3b

  have hTD : T * ‖dF‖ ^ 4 ≠ 0 := by
    intro h0
    have : T * a * ‖dF‖ ^ 4 = 0 := by
      rw [mul_comm T a, mul_assoc, h0, mul_zero]
    rw [this] at k3b
    exact zero_ne_one k3b
  have hab : a = b * P := by
    have h1 : T * ‖dF‖ ^ 4 * a = T * ‖dF‖ ^ 4 * (b * P) := by
      calc T * ‖dF‖ ^ 4 * a = T * a * ‖dF‖ ^ 4 := by ring
        _ = 1 := k3b
        _ = T * b * (‖dF‖ ^ 4 * P) := k3a.symm
        _ = T * ‖dF‖ ^ 4 * (b * P) := by ring
    exact mul_left_cancel₀ hTD h1
  calc q ^ 2 * a ^ 2 * g = q ^ 2 * (b * P) ^ 2 * g := by rw [hab]
    _ = b ^ 2 * (g * P ^ 2 * q ^ 2) := by ring
    _ = b ^ 2 * ‖(16 : F)‖ := by rw [hgram]
    _ = ‖(16 : F)‖ * b ^ 2 := by ring

end Main

end P2mE8Last2

end

open MeasureTheory NumberField IsDedekindDomain AutomorphicForm
open scoped TensorProduct TensorProduct.RightActions ENNReal

theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (h2 : Module.finrank K L = 2) (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (δ₀ : GL (Fin 2) L)
    {κ : Type} [Fintype κ] [DecidableEq κ] (hκ : Fintype.card κ = 4)
    (x : κ → Matrix (Fin 2) (Fin 2) L) (hx : LinearIndependent K x)
    (hspan : ∀ X : Matrix (Fin 2) (Fin 2) L,
      X * (δ₀ : Matrix (Fin 2) (Fin 2) L) = (δ₀ : Matrix (Fin 2) (Fin 2) L) * X.map σ ↔
        X ∈ Submodule.span K (Set.range x))
    (v : HeightOneSpectrum (𝓞 K))
    (hdiv : ∀ X ∈ twistedCommutant K L (v.adicCompletion K) σ
        (Matrix.GeneralLinearGroup.map
          (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] v.adicCompletion K) δ₀),
      X ≠ 0 → IsUnit X) :
    ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ 2 *
      ((AddSubgroup.closure
          {X : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K) |
            ∃ (i : κ) (a : v.adicCompletion K), a ∈ v.adicCompletionIntegers K ∧
              X = (x i).map (fun l : L => l ⊗ₜ[K] a)}).relIndex
        (AddSubgroup.closure
          {X : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K) |
            X ∈ twistedCommutant K L (v.adicCompletion K) σ
                (Matrix.GeneralLinearGroup.map
                  (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] v.adicCompletion K) δ₀) ∧
              ∃ a : v.adicCompletion K, a ∈ v.adicCompletionIntegers K ∧ X.det = (1 : L) ⊗ₜ[K] a}) : ℝ) ^ 2 *
      ‖algebraMap K (v.adicCompletion K)
          (Matrix.of fun i j : κ => Algebra.trace K L (Matrix.trace (x i * x j))).det‖ =
    ‖(16 : v.adicCompletion K)‖ *
      ((AddSubgroup.closure
          {X : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K) |
            X ∈ twistedCommutant K L (v.adicCompletion K) σ
                (Matrix.GeneralLinearGroup.map
                  (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] v.adicCompletion K) δ₀) ∧
              ∃ a : v.adicCompletion K, a ∈ v.adicCompletionIntegers K ∧ X.det = (1 : L) ⊗ₜ[K] a}).relIndex
        (AddSubgroup.closure
          {X : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K) |
            ∃ (i : κ) (a : v.adicCompletion K), a ∈ v.adicCompletionIntegers K ∧
              X = (x i).map (fun l : L => l ⊗ₜ[K] a)}) : ℝ) ^ 2 :=
  P2mE8Last2.main K L h2 σ hgen δ₀ hκ x hx hspan v hdiv

end S_AutomorphicForm_absNorm_sq_mul_relIndex_sq_mul_norm_det_trace_eq_norm_sixteen_mul_relIndex_sq_of_forall_isUnit
end P2MW
export P2MW.S_AutomorphicForm_absNorm_sq_mul_relIndex_sq_mul_norm_det_trace_eq_norm_sixteen_mul_relIndex_sq_of_forall_isUnit (solution)
