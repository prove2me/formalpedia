-- Prove2me | solution 1 for AutomorphicForm.relIndex_conj_map_integers_sq_mul_norm_det_trace_eq_norm_sixteen_mul_relIndex_sq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/11a0d04d-a13c-5ef8-8dd7-2fd06478b26b

import Definitions.Def_AutomorphicForm_TwistedCommutant
import Definitions.Def_AutomorphicForm_BaseChangePlaces
import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_NumberField_TateGlobalZeta
import Theorems.Thm_IsDedekindDomain_HeightOneSpectrum_relIndex_span_range_mul_norm_det_eq_one_of_forall_mem_span
import Theorems.Thm_AutomorphicForm_exists_homeomorph_twistedCommutant_map_mul_scalar_forall_coe_eq_sum_map_tmul_of_linearIndependent
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_relIndex_conj_map_integers_sq_mul_norm_det_trace_eq_norm_sixteen_mul_relIndex_sq

set_option autoImplicit false

open NumberField IsDedekindDomain AutomorphicForm
open scoped TensorProduct TensorProduct.RightActions

noncomputable section

namespace P2mE8Last1

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

def conjMap (y y' : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) (g : Matrix (Fin 2) (Fin 2) A) :
    Matrix (Fin 2) (Fin 2) (L ⊗[K] A) :=
  y * g.map ⇑(Algebra.TensorProduct.includeRight : A →ₐ[K] L ⊗[K] A) * y'

theorem conjMap_add (y y' : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) (g g' : Matrix (Fin 2) (Fin 2) A) :
    conjMap K L A y y' (g + g') = conjMap K L A y y' g + conjMap K L A y y' g' := by
  unfold conjMap
  rw [Matrix.map_add _ (map_add _), mul_add, add_mul]

theorem map_smul_includeRight (c : A) (g : Matrix (Fin 2) (Fin 2) A) :
    (c • g).map ⇑(Algebra.TensorProduct.includeRight : A →ₐ[K] L ⊗[K] A) =
      c • g.map ⇑(Algebra.TensorProduct.includeRight : A →ₐ[K] L ⊗[K] A) := by
  ext i j
  simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, Algebra.TensorProduct.includeRight_apply]
  rw [rightActions_smul_eq K L A c, Algebra.TensorProduct.tmul_mul_tmul, one_mul]

theorem conjMap_smul (y y' : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) (c : A) (g : Matrix (Fin 2) (Fin 2) A) :
    conjMap K L A y y' (c • g) = c • conjMap K L A y y' g := by
  unfold conjMap
  rw [map_smul_includeRight, Matrix.mul_smul, Matrix.smul_mul]

theorem conjMap_zero (y y' : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) : conjMap K L A y y' 0 = 0 := by
  unfold conjMap
  rw [Matrix.map_zero _ (map_zero _), mul_zero, zero_mul]

theorem conjMap_sum {ι : Type} (s : Finset ι) (y y' : Matrix (Fin 2) (Fin 2) (L ⊗[K] A))
    (g : ι → Matrix (Fin 2) (Fin 2) A) :
    conjMap K L A y y' (∑ i ∈ s, g i) = ∑ i ∈ s, conjMap K L A y y' (g i) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty, Finset.sum_empty, conjMap_zero]
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, conjMap_add, ih]

theorem conjMap_eq_sum (y y' : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) (g : Matrix (Fin 2) (Fin 2) A) :
    conjMap K L A y y' g =
      ∑ p : Fin 2 × Fin 2, g p.1 p.2 • conjMap K L A y y' (Matrix.single p.1 p.2 (1 : A)) := by
  conv_lhs => rw [Matrix.matrix_eq_sum_single g]
  rw [conjMap_sum, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [conjMap_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [← conjMap_smul, Matrix.smul_single, smul_eq_mul, mul_one]

theorem conjMap_injective {y y' : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)} (hy : y' * y = 1) (hy' : y * y' = 1)
    (hinj : Function.Injective (Algebra.TensorProduct.includeRight : A →ₐ[K] L ⊗[K] A))
    {g : Matrix (Fin 2) (Fin 2) A} (hg : conjMap K L A y y' g = 0) : g = 0 := by
  unfold conjMap at hg
  have h : g.map ⇑(Algebra.TensorProduct.includeRight : A →ₐ[K] L ⊗[K] A) = 0 := by
    calc g.map ⇑(Algebra.TensorProduct.includeRight : A →ₐ[K] L ⊗[K] A)
        = (y' * y) * g.map ⇑(Algebra.TensorProduct.includeRight : A →ₐ[K] L ⊗[K] A) * (y' * y) := by
          rw [hy, one_mul, mul_one]
      _ = y' * (y * g.map ⇑(Algebra.TensorProduct.includeRight : A →ₐ[K] L ⊗[K] A) * y') * y := by
          simp only [mul_assoc]
      _ = 0 := by rw [hg, mul_zero, zero_mul]
  ext i j
  have hij := congrFun (congrFun h i) j
  rw [Matrix.map_apply, Matrix.zero_apply] at hij
  rw [Matrix.zero_apply]
  apply hinj
  rw [hij, map_zero]

theorem gram_conjMap_single [FiniteDimensional K L] (y y' : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) (hy : y' * y = 1) :
    gram K L A (fun p : Fin 2 × Fin 2 => conjMap K L A y y' (Matrix.single p.1 p.2 (1 : A))) =
      (Module.finrank K L : A) • Equiv.Perm.permMatrix A (Equiv.prodComm (Fin 2) (Fin 2)) := by
  ext ⟨a, b⟩ ⟨c, d⟩
  rw [gram_apply, bf, Matrix.smul_apply]
  dsimp only [Equiv.Perm.permMatrix]
  simp only [PEquiv.toMatrix_apply, Equiv.toPEquiv_apply, Option.mem_def, Equiv.prodComm_apply, Prod.swap_prod_mk,
    Option.some.injEq, Prod.mk.injEq]
  unfold conjMap
  set ι' := (Algebra.TensorProduct.includeRight : A →ₐ[K] L ⊗[K] A) with hι'
  have hprod : y * (Matrix.single a b (1 : A)).map ⇑ι' * y' * (y * (Matrix.single c d (1 : A)).map ⇑ι' * y') =
      y * ((Matrix.single a b (1 : A) * Matrix.single c d (1 : A)).map ⇑ι') * y' := by
    rw [Matrix.map_mul]
    simp only [mul_assoc]
    rw [← mul_assoc y' y, hy, one_mul]
  rw [hprod, Matrix.trace_mul_comm, ← mul_assoc, hy, one_mul, ← AddMonoidHom.map_trace]
  have htr : ∀ t : A, trF K L A (ι' t) = (Module.finrank K L : A) * t := fun t => by
    rw [hι', Algebra.TensorProduct.includeRight_apply, trF_tmul,
      show (1 : L) = algebraMap K L 1 from (map_one _).symm, Algebra.trace_algebraMap, nsmul_eq_mul, mul_one,
      Algebra.smul_def, map_natCast]
  rw [htr]
  by_cases h : b = c
  · subst h
    rw [Matrix.single_mul_single_same, mul_one]
    by_cases h' : a = d
    · subst h'
      rw [Matrix.trace_single_eq_same, if_pos ⟨rfl, rfl⟩, smul_eq_mul]
    · rw [Matrix.trace_single_eq_of_ne _ _ _ h', if_neg (fun hh => h' hh.2), smul_zero, mul_zero]
  · rw [Matrix.single_mul_single_of_ne _ _ _ _ h, Matrix.trace_zero, if_neg (fun hh => h hh.1), smul_zero,
      mul_zero]

theorem det_gram_conjMap_single [FiniteDimensional K L] (y y' : Matrix (Fin 2) (Fin 2) (L ⊗[K] A))
    (hy : y' * y = 1) :
    (gram K L A (fun p : Fin 2 × Fin 2 => conjMap K L A y y' (Matrix.single p.1 p.2 (1 : A)))).det =
      (Module.finrank K L : A) ^ 4 * ((Equiv.Perm.sign (Equiv.prodComm (Fin 2) (Fin 2)) : ℤ) : A) := by
  rw [gram_conjMap_single K L A y y' hy, Matrix.det_smul, Matrix.det_permutation, Fintype.card_prod,
    Fintype.card_fin]

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

set_option maxHeartbeats 3200000 in

theorem closure_setM_eq (y y' : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) :
    AddSubgroup.closure
        {X : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K) |
          ∃ g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K),
            (∀ i j, g i j ∈ v.adicCompletionIntegers K) ∧
              X = conjMap K L (v.adicCompletion K) y y' g} =
      (Submodule.span (v.adicCompletionIntegers K)
        (Set.range fun p : Fin 2 × Fin 2 =>
          conjMap K L (v.adicCompletion K) y y' (Matrix.single p.1 p.2 (1 : v.adicCompletion K)))).toAddSubgroup := by
  refine closure_eq_span_toAddSubgroup K v _ _ ?_ ?_ ?_
  · rintro X ⟨p, rfl⟩
    refine ⟨Matrix.single p.1 p.2 1, fun i j => ?_, rfl⟩
    rw [Matrix.single_apply]
    split_ifs
    · exact one_mem _
    · exact zero_mem _
  · rintro X ⟨g, hg, rfl⟩
    rw [SetLike.mem_coe, conjMap_eq_sum]
    refine Submodule.sum_mem _ fun p _ => ?_
    rw [show g p.1 p.2 • conjMap K L (v.adicCompletion K) y y' (Matrix.single p.1 p.2 1) =
      (⟨g p.1 p.2, hg p.1 p.2⟩ : v.adicCompletionIntegers K) •
        conjMap K L (v.adicCompletion K) y y' (Matrix.single p.1 p.2 1) from rfl]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨p, rfl⟩)
  · rintro r X ⟨g, hg, rfl⟩
    refine ⟨(r : v.adicCompletion K) • g, fun i j => mul_mem r.2 (hg i j), ?_⟩
    rw [conjMap_smul]
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

theorem norm_intCast_units (F : Type) [NormedField F] (u : ℤˣ) : ‖((u : ℤ) : F)‖ = 1 := by
  rcases Int.units_eq_one_or u with rfl | rfl
  · simp
  · simp

set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 12800000 in
theorem main
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (h2 : Module.finrank K L = 2) (σ : L ≃ₐ[K] L)
    (δ₀ : GL (Fin 2) L)
    {κ : Type} [Fintype κ] [DecidableEq κ] (hκ : Fintype.card κ = 4)
    (x : κ → Matrix (Fin 2) (Fin 2) L) (hx : LinearIndependent K x)
    (hspan : ∀ X : Matrix (Fin 2) (Fin 2) L,
      X * (δ₀ : Matrix (Fin 2) (Fin 2) L) = (δ₀ : Matrix (Fin 2) (Fin 2) L) * X.map σ ↔
        X ∈ Submodule.span K (Set.range x))
    (v : HeightOneSpectrum (𝓞 K))
    (y : GL (Fin 2) (L ⊗[K] v.adicCompletion K))
    (hy : ∀ g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K),
      (y : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) *
          g.map (Algebra.TensorProduct.includeRight : v.adicCompletion K →ₐ[K] L ⊗[K] v.adicCompletion K) *
          ((y⁻¹ : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) ∈
        twistedCommutant K L (v.adicCompletion K) σ
          (Matrix.GeneralLinearGroup.map
            (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] v.adicCompletion K) δ₀)) :
    let SΛ : AddSubgroup (Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) :=
      AddSubgroup.closure
        {X : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K) |
          ∃ (i : κ) (a : v.adicCompletion K), a ∈ v.adicCompletionIntegers K ∧
            X = (x i).map (fun l : L => l ⊗ₜ[K] a)}
    let SM : AddSubgroup (Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) :=
      AddSubgroup.closure
        {X : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K) |
          ∃ g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K),
            (∀ i j, g i j ∈ v.adicCompletionIntegers K) ∧
              X = (y : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) *
                g.map (Algebra.TensorProduct.includeRight :
                  v.adicCompletion K →ₐ[K] L ⊗[K] v.adicCompletion K) *
                ((y⁻¹ : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) :
                  Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K))}
    (SΛ.relIndex SM : ℝ) ^ 2 *
        ‖algebraMap K (v.adicCompletion K)
          (Matrix.of fun i j : κ => Algebra.trace K L (Matrix.trace (x i * x j))).det‖ =
      ‖(16 : v.adicCompletion K)‖ * (SM.relIndex SΛ : ℝ) ^ 2 := by
  intro SΛ SM

  set F := v.adicCompletion K with hF
  set O := v.adicCompletionIntegers K with hO
  set yM : Matrix (Fin 2) (Fin 2) (L ⊗[K] F) := (y : Matrix (Fin 2) (Fin 2) (L ⊗[K] F)) with hyM
  set yM' : Matrix (Fin 2) (Fin 2) (L ⊗[K] F) :=
    ((y⁻¹ : GL (Fin 2) (L ⊗[K] F)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] F)) with hyM'
  have hyy : yM' * yM = 1 := y.inv_mul
  have hyy' : yM * yM' = 1 := y.mul_inv
  have hinjF : Function.Injective (Algebra.TensorProduct.includeRight : F →ₐ[K] L ⊗[K] F) :=
    (algebraMap F (L ⊗[K] F)).injective

  set bx : κ → Matrix (Fin 2) (Fin 2) (L ⊗[K] F) := fun i => (x i).map (fun l : L => l ⊗ₜ[K] (1 : F)) with hbx
  set f : Fin 2 × Fin 2 → Matrix (Fin 2) (Fin 2) (L ⊗[K] F) :=
    fun p => conjMap K L F yM yM' (Matrix.single p.1 p.2 (1 : F)) with hf
  haveI : Nonempty κ := by
    rw [← Fintype.card_pos_iff, hκ]; norm_num
  obtain ⟨eκ⟩ : Nonempty (κ ≃ Fin 2 × Fin 2) :=
    ⟨Fintype.equivOfCardEq (by rw [hκ, Fintype.card_prod, Fintype.card_fin])⟩
  set fκ : κ → Matrix (Fin 2) (Fin 2) (L ⊗[K] F) := f ∘ eκ with hfκ

  obtain ⟨e, he⟩ :=
    AutomorphicForm.exists_homeomorph_twistedCommutant_map_mul_scalar_forall_coe_eq_sum_map_tmul_of_linearIndependent
      K L F σ δ₀ 1 κ x hx hspan
  have hδ : Matrix.GeneralLinearGroup.map
        (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] F) δ₀ *
      Matrix.GeneralLinearGroup.scalar (Fin 2) (1 : (L ⊗[K] F)ˣ) =
      Matrix.GeneralLinearGroup.map (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] F) δ₀ := by
    rw [map_one, mul_one]
  have hsum : ∀ a : κ → F, ∑ i, (x i).map (fun l : L => l ⊗ₜ[K] a i) = ∑ i, a i • bx i := fun a =>
    Finset.sum_congr rfl fun i _ => map_tmul_eq_smul K L v (x i) (a i)
  have hmemW : ∀ X ∈ twistedCommutant K L F σ
      (Matrix.GeneralLinearGroup.map (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] F) δ₀),
      X ∈ Submodule.span F (Set.range bx) := by
    intro X hX
    rw [← hδ] at hX
    have hXe : X = ((e (e.symm ⟨X, hX⟩) : twistedCommutant K L F σ _) : Matrix (Fin 2) (Fin 2) (L ⊗[K] F)) := by
      rw [Homeomorph.apply_symm_apply]
    rw [hXe, he, hsum]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  have hli : LinearIndependent F bx := by
    rw [Fintype.linearIndependent_iff]
    intro a ha
    have h0 : e a = e 0 := by
      apply Subtype.ext
      rw [he, he, hsum, hsum, ha]
      simp
    have := e.injective h0
    exact fun i => congrFun this i
  set W : Submodule F (Matrix (Fin 2) (Fin 2) (L ⊗[K] F)) := Submodule.span F (Set.range bx) with hW
  letI instOW : Module O W := Submodule.module' W
  haveI instOFW : IsScalarTower O F W := Submodule.isScalarTower W
  let b₂ : Module.Basis κ F W := Module.Basis.span hli
  have hb₂ : ∀ i, (b₂ i : Matrix (Fin 2) (Fin 2) (L ⊗[K] F)) = bx i := fun i => by
    rw [Module.Basis.span_apply]

  have hfW : ∀ p, f p ∈ W := fun p => hmemW _ (hy (Matrix.single p.1 p.2 1))
  have hlif : LinearIndependent F f := by
    rw [Fintype.linearIndependent_iff]
    intro c hc
    have hsum' : ∑ p, c p • f p = conjMap K L F yM yM' (Matrix.of fun a b => c (a, b)) := by
      rw [conjMap_eq_sum]
      rfl
    rw [hsum'] at hc
    have h0 := conjMap_injective K L F hyy hyy' hinjF hc
    intro p
    have := congrFun (congrFun h0 p.1) p.2
    rwa [Matrix.of_apply, Matrix.zero_apply] at this
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
    show AddSubgroup.closure {X : Matrix (Fin 2) (Fin 2) (L ⊗[K] F) |
          ∃ g : Matrix (Fin 2) (Fin 2) F, (∀ i j, g i j ∈ O) ∧ X = conjMap K L F yM yM' g} = MM
    rw [closure_setM_eq K L v yM yM', hMM, hfκ, eκ.surjective.range_comp]
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
  have hgram₂ : (gram K L F fκ).det =
      (2 : F) ^ 4 * ((Equiv.Perm.sign (Equiv.prodComm (Fin 2) (Fin 2)) : ℤ) : F) := by
    rw [hfκ, gram_reindex, Matrix.det_submatrix_equiv_self, hf, det_gram_conjMap_single K L F yM yM' hyy, h2,
      Nat.cast_ofNat]
  have hgram : ‖algebraMap K F (Matrix.of fun i j : κ => Algebra.trace K L (Matrix.trace (x i * x j))).det‖ *
      ‖b₂.det b₁‖ ^ 2 = ‖(16 : F)‖ := by
    have := hgram₁.symm.trans hgram₂
    have hn := congrArg (fun z : F => ‖z‖) this
    simp only [norm_mul, norm_pow] at hn
    rw [norm_intCast_units, mul_one, show ‖(2 : F)‖ ^ 4 = ‖(2 : F) ^ 4‖ from (norm_pow _ _).symm] at hn
    rw [mul_comm, hn]
    norm_num

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
  calc a ^ 2 * g = (b * P) ^ 2 * g := by rw [hab]
    _ = b ^ 2 * (g * P ^ 2) := by ring
    _ = b ^ 2 * ‖(16 : F)‖ := by rw [hgram]
    _ = ‖(16 : F)‖ * b ^ 2 := by ring

end Main

end P2mE8Last1

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
    (y : GL (Fin 2) (L ⊗[K] v.adicCompletion K))
    (hy : ∀ g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K),
      (y : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) *
          g.map (Algebra.TensorProduct.includeRight : v.adicCompletion K →ₐ[K] L ⊗[K] v.adicCompletion K) *
          ((y⁻¹ : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) ∈
        twistedCommutant K L (v.adicCompletion K) σ
          (Matrix.GeneralLinearGroup.map
            (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] v.adicCompletion K) δ₀)) :
    ((AddSubgroup.closure
          {X : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K) |
            ∃ (i : κ) (a : v.adicCompletion K), a ∈ v.adicCompletionIntegers K ∧
              X = (x i).map (fun l : L => l ⊗ₜ[K] a)}).relIndex
        (AddSubgroup.closure
          {X : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K) |
            ∃ g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K),
              (∀ i j, g i j ∈ v.adicCompletionIntegers K) ∧
              X = (y : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) *
                g.map (Algebra.TensorProduct.includeRight :
                  v.adicCompletion K →ₐ[K] L ⊗[K] v.adicCompletion K) *
                ((y⁻¹ : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) :
                  Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K))}) : ℝ) ^ 2 *
      ‖algebraMap K (v.adicCompletion K)
          (Matrix.of fun i j : κ => Algebra.trace K L (Matrix.trace (x i * x j))).det‖ =
    ‖(16 : v.adicCompletion K)‖ *
      ((AddSubgroup.closure
          {X : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K) |
            ∃ g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K),
              (∀ i j, g i j ∈ v.adicCompletionIntegers K) ∧
              X = (y : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) *
                g.map (Algebra.TensorProduct.includeRight :
                  v.adicCompletion K →ₐ[K] L ⊗[K] v.adicCompletion K) *
                ((y⁻¹ : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) :
                  Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K))}).relIndex
        (AddSubgroup.closure
          {X : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K) |
            ∃ (i : κ) (a : v.adicCompletion K), a ∈ v.adicCompletionIntegers K ∧
              X = (x i).map (fun l : L => l ⊗ₜ[K] a)}) : ℝ) ^ 2 :=
  P2mE8Last1.main K L h2 σ δ₀ hκ x hx hspan v y hy

end S_AutomorphicForm_relIndex_conj_map_integers_sq_mul_norm_det_trace_eq_norm_sixteen_mul_relIndex_sq
end P2MW
export P2MW.S_AutomorphicForm_relIndex_conj_map_integers_sq_mul_norm_det_trace_eq_norm_sixteen_mul_relIndex_sq (solution)
