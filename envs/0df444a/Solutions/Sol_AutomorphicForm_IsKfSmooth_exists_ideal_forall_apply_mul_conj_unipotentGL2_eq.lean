-- Prove2me | solution 1 for AutomorphicForm.IsKfSmooth.exists_ideal_forall_apply_mul_conj_unipotentGL2_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/a0651323-a6ce-52bd-88e1-53668471b377

import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_IsKfSmooth_exists_ideal_forall_apply_mul_conj_unipotentGL2_eq

set_option autoImplicit false

open NumberField NumberField.AdelicLevel AutomorphicForm FLT.SmoothVectors IsDedekindDomain
open scoped Topology

namespace KfLevelSol

section NumberFieldAdelic

variable (F : Type) [Field F] [NumberField F]

variable {F} in
theorem idealBound_span_singleton {r : 𝓞 F} (hr : r ≠ 0) (v : HeightOneSpectrum (𝓞 F)) :
    idealBound (𝓞 F) (Ideal.span {r}) v = v.intValuation r := by
  rw [idealBound_of_ne_bot (fun h => hr (Ideal.span_singleton_eq_bot.mp h)) v, v.intValuation_if_neg hr]

theorem exp_neg_one_pow (e : ℕ) :
    (WithZero.exp (-1 : ℤ)) ^ e = WithZero.exp (-(e : ℤ)) := by
  induction e with
  | zero => simp
  | succ n ih => rw [pow_succ, ih, ← WithZero.exp_add]; congr 1; push_cast; ring

variable {F} in
theorem neg_mem_idealBall {N : Ideal (𝓞 F)} {y : FiniteAdeleRing (𝓞 F) F} (hy : y ∈ idealBall (𝓞 F) F N) :
    -y ∈ idealBall (𝓞 F) F N := fun v => by
  rw [coe_neg_apply, Valuation.map_neg]; exact hy v

def sm (z : Π v : HeightOneSpectrum (𝓞 F), v.adicCompletionIntegers F) : FiniteAdeleRing (𝓞 F) F :=
  RestrictedProduct.structureMap (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
    (fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F))) Filter.cofinite z

theorem sm_apply (z : Π v : HeightOneSpectrum (𝓞 F), v.adicCompletionIntegers F) (v : HeightOneSpectrum (𝓞 F)) :
    sm F z v = (z v : v.adicCompletion F) := rfl

theorem sm_zero : sm F 0 = 0 := RestrictedProduct.ext _ _ fun _ => rfl

theorem nhds_zero_eq_map_sm : 𝓝 (0 : FiniteAdeleRing (𝓞 F) F) = Filter.map (sm F) (𝓝 0) := by
  have hopen : ∀ v : HeightOneSpectrum (𝓞 F), IsOpen ((v.adicCompletionIntegers F : Set (v.adicCompletion F))) :=
    fun v => Valued.isOpen_valuationSubring _
  rw [← sm_zero F]
  exact RestrictedProduct.nhds_zero_eq_map_structureMap (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
    (B := fun v => v.adicCompletionIntegers F) hopen

theorem exists_exp_neg_ball_subset (v : HeightOneSpectrum (𝓞 F)) {U : Set (v.adicCompletionIntegers F)}
    (hU : U ∈ 𝓝 (0 : v.adicCompletionIntegers F)) :
    ∃ e : ℕ, ∀ y : v.adicCompletionIntegers F,
      Valued.v (y : v.adicCompletion F) ≤ WithZero.exp (-(e : ℤ)) → y ∈ U := by
  obtain ⟨u, hu, huU⟩ := (mem_nhds_subtype _ _ _).mp hU
  change u ∈ 𝓝 (0 : v.adicCompletion F) at hu
  obtain ⟨γ, hγ⟩ := Valued.mem_nhds_zero.mp hu
  obtain ⟨t, ht⟩ := MonoidWithZeroHom.ValueGroup₀.restrict₀_surjective
    (MonoidWithZeroHom.ofClass (Valued.v : Valuation (v.adicCompletion F) (WithZero (Multiplicative ℤ)))) γ.1
  have hvt : Valued.v t ≠ 0 := by
    intro h
    apply γ.ne_zero
    rw [← ht, MonoidWithZeroHom.ValueGroup₀.restrict₀_eq_zero_iff]
    exact h
  obtain ⟨m, hm⟩ : ∃ m : ℤ, Valued.v t = WithZero.exp m := ⟨_, (WithZero.exp_log hvt).symm⟩
  refine ⟨(-m).toNat + 1, fun y hy => huU ?_⟩
  show (y : v.adicCompletion F) ∈ u
  apply hγ
  show Valued.v.restrict (y : v.adicCompletion F) < γ.1
  have hlt : Valued.v (y : v.adicCompletion F) < Valued.v t := by
    refine lt_of_le_of_lt hy ?_
    rw [hm, WithZero.exp_lt_exp]
    have := Int.self_le_toNat (-m)
    omega
  have h2 : Valued.v.restrict (y : v.adicCompletion F) < Valued.v.restrict t :=
    Valued.v.restrict_lt_iff.mpr hlt
  rw [← ht]
  exact h2

theorem exists_idealBall_subset_of_mem_nhds_zero {B : Set (FiniteAdeleRing (𝓞 F) F)}
    (hB : B ∈ 𝓝 (0 : FiniteAdeleRing (𝓞 F) F)) : ∃ N : Ideal (𝓞 F), N ≠ ⊥ ∧ idealBall (𝓞 F) F N ⊆ B := by
  classical
  rw [nhds_zero_eq_map_sm F, Filter.mem_map, nhds_pi, Filter.mem_pi'] at hB
  obtain ⟨I, t, ht, hIB⟩ := hB
  choose e he using fun v : HeightOneSpectrum (𝓞 F) => exists_exp_neg_ball_subset F v (ht v)
  choose π hπ using fun v : HeightOneSpectrum (𝓞 F) => v.intValuation_exists_uniformizer
  have hπ0 : ∀ v, π v ≠ 0 := fun v h => by
    have h1 := hπ v
    rw [h, map_zero] at h1
    exact WithZero.exp_ne_zero h1.symm
  have hr0 : (∏ v ∈ I, π v ^ e v) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun v _ => pow_ne_zero _ (hπ0 v)
  refine ⟨Ideal.span {∏ v ∈ I, π v ^ e v}, fun h => hr0 (Ideal.span_singleton_eq_bot.mp h), fun x hx => ?_⟩
  have hxint : x ∈ integralFiniteAdeles (𝓞 F) F := idealBall_subset_integralFiniteAdeles _ hx
  let y : Π v : HeightOneSpectrum (𝓞 F), v.adicCompletionIntegers F := fun v => ⟨x v, hxint v⟩
  have hyx : sm F y = x := RestrictedProduct.ext _ _ fun _ => rfl
  have hy : y ∈ Set.pi (↑I) t := by
    intro w hw
    apply he w
    show Valued.v (x w) ≤ WithZero.exp (-(e w : ℤ))
    have hxw : Valued.v (x w) ≤ idealBound (𝓞 F) (Ideal.span {∏ v ∈ I, π v ^ e v}) w := hx w
    rw [idealBound_span_singleton hr0] at hxw
    refine hxw.trans ?_
    rw [← Finset.mul_prod_erase I (fun v => π v ^ e v) (Finset.mem_coe.mp hw), map_mul, map_pow, hπ w,
      exp_neg_one_pow]
    calc WithZero.exp (-(e w : ℤ)) * w.intValuation (∏ v ∈ I.erase w, π v ^ e v)
        ≤ WithZero.exp (-(e w : ℤ)) * 1 := mul_le_mul_right (w.intValuation_le_one _) _
      _ = WithZero.exp (-(e w : ℤ)) := mul_one _
  have hmem : sm F y ∈ B := hIB hy
  rwa [hyx] at hmem

noncomputable def levelParam (f : Bool × Fin 2 × Fin 2 → FiniteAdeleRing (𝓞 F) F) (b : Bool) :
    Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F) :=
  Matrix.of fun i j => (((1 : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) i j,
    (1 : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) i j + f (b, i, j)) : AdeleRing (𝓞 F) F)

theorem continuous_levelParam (b : Bool) :
    Continuous fun f : Bool × Fin 2 × Fin 2 → FiniteAdeleRing (𝓞 F) F => levelParam F f b := by
  refine continuous_matrix fun i j => ?_
  show Continuous fun f : Bool × Fin 2 × Fin 2 → FiniteAdeleRing (𝓞 F) F =>
    ((((1 : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) i j,
      (1 : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) i j + f (b, i, j)) : AdeleRing (𝓞 F) F))
  have h1 : Continuous fun _ : Bool × Fin 2 × Fin 2 → FiniteAdeleRing (𝓞 F) F =>
      (1 : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) i j := continuous_const
  have h2 : Continuous fun f : Bool × Fin 2 × Fin 2 → FiniteAdeleRing (𝓞 F) F =>
      (1 : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) i j + f (b, i, j) :=
    continuous_const.add
      (continuous_apply (b, i, j) : Continuous fun p : Bool × Fin 2 × Fin 2 → FiniteAdeleRing (𝓞 F) F => p (b, i, j))
  exact h1.prodMk h2

theorem continuous_levelParamPair : Continuous fun f : Bool × Fin 2 × Fin 2 → FiniteAdeleRing (𝓞 F) F =>
    (levelParam F f true, MulOpposite.op (levelParam F f false)) :=
  (continuous_levelParam F true).prodMk (MulOpposite.continuous_op.comp (continuous_levelParam F false))

theorem levelParam_zero (b : Bool) : levelParam F 0 b = 1 := by
  refine Matrix.ext fun i j => ?_
  simp only [levelParam, Matrix.of_apply, Pi.zero_apply, add_zero]
  rw [Matrix.one_apply, Matrix.one_apply, Matrix.one_apply]
  split_ifs <;> rfl

theorem exists_ideal_level_subset_of_mem_nhds_one {W : Set (GL (Fin 2) (AdeleRing (𝓞 F) F))}
    (hW : W ∈ 𝓝 (1 : GL (Fin 2) (AdeleRing (𝓞 F) F))) :
    ∃ N : Ideal (𝓞 F), N ≠ ⊥ ∧ ∀ g : GL (Fin 2) (AdeleRing (𝓞 F) F), glArch (𝓞 F) F g = 1 →
      (∀ i j, (glFin (𝓞 F) F g : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) i j
        - (1 : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) i j ∈ idealBall (𝓞 F) F N) →
      (∀ i j, (((glFin (𝓞 F) F g)⁻¹ : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F)) : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) i j
        - (1 : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) i j ∈ idealBall (𝓞 F) F N) →
      g ∈ W := by
  classical
  rw [Units.isInducing_embedProduct.nhds_eq_comap, Filter.mem_comap] at hW
  obtain ⟨O, hO, hOW⟩ := hW
  rw [map_one] at hO
  have h1 : ((levelParam F 0 true, MulOpposite.op (levelParam F 0 false)) :
      Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F) × (Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F))ᵐᵒᵖ) = 1 := by
    rw [levelParam_zero, levelParam_zero, MulOpposite.op_one]; rfl
  have hO' : (fun f : Bool × Fin 2 × Fin 2 → FiniteAdeleRing (𝓞 F) F =>
      (levelParam F f true, MulOpposite.op (levelParam F f false))) ⁻¹' O ∈
        𝓝 (0 : Bool × Fin 2 × Fin 2 → FiniteAdeleRing (𝓞 F) F) := by
    refine (continuous_levelParamPair F).continuousAt.preimage_mem_nhds ?_
    show O ∈ 𝓝 ((levelParam F 0 true, MulOpposite.op (levelParam F 0 false)))
    rw [h1]; exact hO
  rw [nhds_pi, Filter.mem_pi'] at hO'
  obtain ⟨I, t, ht, hIO⟩ := hO'
  have hD : (⋂ k, t k) ∈ 𝓝 (0 : FiniteAdeleRing (𝓞 F) F) := Filter.iInter_mem.mpr fun k => ht k
  obtain ⟨N, hN, hNB⟩ := exists_idealBall_subset_of_mem_nhds_zero F hD
  refine ⟨N, hN, fun g hg hg1 hg2 => ?_⟩
  let f : Bool × Fin 2 × Fin 2 → FiniteAdeleRing (𝓞 F) F := fun k => match k with
    | (true, i, j) => (glFin (𝓞 F) F g : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) i j
        - (1 : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) i j
    | (false, i, j) => (((glFin (𝓞 F) F g)⁻¹ : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F)) :
        Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) i j
        - (1 : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) i j
  have hf : f ∈ Set.pi (↑I) t := fun k _ => by
    have hk : f k ∈ idealBall (𝓞 F) F N := by
      obtain ⟨b, i, j⟩ := k
      cases b
      · exact hg2 i j
      · exact hg1 i j
    exact Set.mem_iInter.mp (hNB hk) k
  have hmem := hIO hf
  apply hOW
  show Units.embedProduct _ g ∈ O
  rw [Units.embedProduct_apply]
  have hval : (g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) = levelParam F f true := by
    refine Matrix.ext fun i j => Prod.ext ?_ ?_
    · show ((g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) i j).1
        = (1 : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) i j
      rw [← glArch_apply, hg, Units.val_one]
    · show ((g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) i j).2
        = (1 : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) i j
          + ((glFin (𝓞 F) F g : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) i j
            - (1 : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) i j)
      rw [← glFin_apply, add_sub_cancel]
  have hinv : ((g⁻¹ : GL (Fin 2) (AdeleRing (𝓞 F) F)) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F))
      = levelParam F f false := by
    refine Matrix.ext fun i j => Prod.ext ?_ ?_
    · show (((g⁻¹ : GL (Fin 2) (AdeleRing (𝓞 F) F)) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) i j).1
        = (1 : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) i j
      rw [← glArch_apply, map_inv, hg, inv_one, Units.val_one]
    · show (((g⁻¹ : GL (Fin 2) (AdeleRing (𝓞 F) F)) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) i j).2
        = (1 : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) i j
          + ((((glFin (𝓞 F) F g)⁻¹ : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F)) :
              Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) i j
            - (1 : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) i j)
      rw [← glFin_apply, map_inv, add_sub_cancel]
  rw [hval, hinv]
  exact hmem

section Conj

variable {A : Type*} [CommRing A]

theorem unipotentGL2_inv_eq (y : A) : (unipotentGL2 y)⁻¹ = unipotentGL2 (-y) :=
  inv_eq_of_mul_eq_one_right (by rw [← unipotentGL2_add, add_neg_cancel, unipotentGL2_zero])

theorem conj_unipotentGL2_inv (k : GL (Fin 2) A) (y : A) :
    (k⁻¹ * unipotentGL2 y * k)⁻¹ = k⁻¹ * unipotentGL2 (-y) * k := by
  rw [mul_inv_rev, mul_inv_rev, inv_inv, unipotentGL2_inv_eq, mul_assoc]

theorem coe_conj_unipotentGL2_sub_one (k : GL (Fin 2) A) (y : A) :
    ((k⁻¹ * unipotentGL2 y * k : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A) - 1
      = ((k⁻¹ : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A) * (!![1, y; 0, 1] - 1)
          * (k : Matrix (Fin 2) (Fin 2) A) := by
  rw [Units.val_mul, Units.val_mul, unipotentGL2_coe, mul_sub, sub_mul, mul_one, Units.inv_mul]

theorem conj_unipotentGL2_sub_one_apply (k : GL (Fin 2) A) (y : A) (i j : Fin 2) :
    ((k⁻¹ * unipotentGL2 y * k : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A) i j
        - (1 : Matrix (Fin 2) (Fin 2) A) i j
      = ((k⁻¹ : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A) i 0 * y * (k : Matrix (Fin 2) (Fin 2) A) 1 j := by
  have h := congrFun (congrFun (coe_conj_unipotentGL2_sub_one k y) i) j
  rw [Matrix.sub_apply] at h
  rw [h]
  have hE : (!![1, y; 0, 1] - 1 : Matrix (Fin 2) (Fin 2) A) = !![0, y; 0, 0] := by
    ext a b
    fin_cases a <;> fin_cases b <;> simp
  rw [hE]
  fin_cases i <;> fin_cases j <;>
    simp only [Matrix.mul_apply, Fin.sum_univ_two, Fin.zero_eta, Fin.mk_one, Fin.isValue, Matrix.of_apply,
      Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
      Matrix.cons_val_fin_one] <;> ring

end Conj

theorem glArch_unipotentGL2 (t : AdeleRing (𝓞 F) F) :
    glArch (𝓞 F) F (unipotentGL2 t) = unipotentGL2 (adeleArch (𝓞 F) F t) := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  rw [glArch_apply, unipotentGL2_coe, unipotentGL2_coe]
  fin_cases i <;> fin_cases j <;> rfl

theorem glFin_unipotentGL2 (t : AdeleRing (𝓞 F) F) :
    glFin (𝓞 F) F (unipotentGL2 t) = unipotentGL2 (adeleFin (𝓞 F) F t) := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  rw [glFin_apply, unipotentGL2_coe, unipotentGL2_coe]
  fin_cases i <;> fin_cases j <;> rfl

variable {F}

theorem glArch_conj_unipotentGL2 (x : GL (Fin 2) (AdeleRing (𝓞 F) F)) {t : AdeleRing (𝓞 F) F}
    (ht : adeleArch (𝓞 F) F t = 0) : glArch (𝓞 F) F (x⁻¹ * unipotentGL2 t * x) = 1 := by
  rw [map_mul, map_mul, map_inv, glArch_unipotentGL2, ht, unipotentGL2_zero, mul_one, inv_mul_cancel]

theorem glFin_conj_unipotentGL2_sub_one_mem {N : Ideal (𝓞 F)} (x : GL (Fin 2) (AdeleRing (𝓞 F) F))
    (hx : glFin (𝓞 F) F x ∈ finiteIntegralGL2 (𝓞 F) F) {t : AdeleRing (𝓞 F) F} (ht : adeleFin (𝓞 F) F t ∈ idealBall (𝓞 F) F N)
    (i j : Fin 2) :
    (glFin (𝓞 F) F (x⁻¹ * unipotentGL2 t * x) : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) i j
      - (1 : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) i j ∈ idealBall (𝓞 F) F N := by
  rw [map_mul, map_mul, map_inv, glFin_unipotentGL2, conj_unipotentGL2_sub_one_apply]
  exact mul_mem_idealBall_right (mul_mem_idealBall_left ((mem_finiteIntegralGL2_iff.mp hx).2 i 0) ht)
    ((mem_finiteIntegralGL2_iff.mp hx).1 1 j)

theorem glFin_conj_unipotentGL2_inv_sub_one_mem {N : Ideal (𝓞 F)} (x : GL (Fin 2) (AdeleRing (𝓞 F) F))
    (hx : glFin (𝓞 F) F x ∈ finiteIntegralGL2 (𝓞 F) F) {t : AdeleRing (𝓞 F) F} (ht : adeleFin (𝓞 F) F t ∈ idealBall (𝓞 F) F N)
    (i j : Fin 2) :
    (((glFin (𝓞 F) F (x⁻¹ * unipotentGL2 t * x))⁻¹ : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F)) :
      Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) i j
      - (1 : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) i j ∈ idealBall (𝓞 F) F N := by
  rw [map_mul, map_mul, map_inv, glFin_unipotentGL2, conj_unipotentGL2_inv, conj_unipotentGL2_sub_one_apply]
  exact mul_mem_idealBall_right
    (mul_mem_idealBall_left ((mem_finiteIntegralGL2_iff.mp hx).2 i 0) (neg_mem_idealBall ht))
    ((mem_finiteIntegralGL2_iff.mp hx).1 1 j)

end NumberFieldAdelic

section Row

variable {F : Type} [Field F] [NumberField F]

theorem exists_ideal_forall_apply_mul_eq_of_level {φ : AdelicGL2 (𝓞 F) F → ℂ} (hφ : IsKfSmooth F φ) :
    ∃ 𝔫 : Ideal (𝓞 F), 𝔫 ≠ ⊥ ∧ ∀ k : AdelicGL2 (𝓞 F) F, glArch (𝓞 F) F k = 1 →
      (∀ i j, (glFin (𝓞 F) F k : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) i j
        - (1 : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) i j ∈ idealBall (𝓞 F) F 𝔫) →
      (∀ i j, (((glFin (𝓞 F) F k)⁻¹ : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F)) : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) i j
        - (1 : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) i j ∈ idealBall (𝓞 F) F 𝔫) →
      ∀ g : AdelicGL2 (𝓞 F) F, φ (g * k) = φ g := by
  have hopen : IsOpen ((MulAction.stabilizer (finiteAdelicGL2Subgroup F)
      (RightTranslationFn.mk φ : RightTranslationFn (AdelicGL2 (𝓞 F) F) ℂ) :
        Subgroup (finiteAdelicGL2Subgroup F)) : Set (finiteAdelicGL2Subgroup F)) := hφ
  obtain ⟨W, hWo, hWeq⟩ := isOpen_induced_iff.mp hopen
  have h1W : (1 : AdelicGL2 (𝓞 F) F) ∈ W := by
    have h1 : (1 : finiteAdelicGL2Subgroup F) ∈ Subtype.val ⁻¹' W := by
      rw [hWeq]; exact Subgroup.one_mem _
    exact h1
  obtain ⟨𝔫, h𝔫, hlevel⟩ := exists_ideal_level_subset_of_mem_nhds_one F (hWo.mem_nhds h1W)
  refine ⟨𝔫, h𝔫, fun k hk hk1 hk2 g => ?_⟩
  have hkW : k ∈ W := hlevel k hk hk1 hk2
  have hkfin : k ∈ finiteAdelicGL2Subgroup F := (mem_finiteAdelicGL2Subgroup_iff F k).mpr hk
  have hstab : (⟨k, hkfin⟩ : finiteAdelicGL2Subgroup F) ∈ MulAction.stabilizer (finiteAdelicGL2Subgroup F)
      (RightTranslationFn.mk φ : RightTranslationFn (AdelicGL2 (𝓞 F) F) ℂ) := by
    rw [← SetLike.mem_coe, ← hWeq]; exact hkW
  have h := congrArg (fun f : RightTranslationFn (AdelicGL2 (𝓞 F) F) ℂ => RightTranslationFn.toFun f g)
    (MulAction.mem_stabilizer_iff.mp hstab)
  rw [Subgroup.smul_def, RightTranslationFn.toFun_smul, RightTranslationFn.toFun_mk] at h
  exact h

end Row

end KfLevelSol

open AutomorphicForm in
theorem solution
    {F : Type} [Field F] [NumberField F] {φ : AdelicGL2 (𝓞 F) F → ℂ} (hφ : IsKfSmooth F φ) :
    ∃ 𝔫 : Ideal (𝓞 F), 𝔫 ≠ ⊥ ∧
      ∀ (g x : AdelicGL2 (𝓞 F) F), glFin (𝓞 F) F x ∈ finiteIntegralGL2 (𝓞 F) F →
      ∀ (t : AdeleRing (𝓞 F) F), adeleArch (𝓞 F) F t = 0 →
        adeleFin (𝓞 F) F t ∈ idealBall (𝓞 F) F 𝔫 →
          φ (g * (x⁻¹ * unipotentGL2 t * x)) = φ g := by
  obtain ⟨𝔫, h𝔫, hlevel⟩ := KfLevelSol.exists_ideal_forall_apply_mul_eq_of_level hφ
  exact ⟨𝔫, h𝔫, fun g x hx t ht0 htN => hlevel _ (KfLevelSol.glArch_conj_unipotentGL2 x ht0)
    (KfLevelSol.glFin_conj_unipotentGL2_sub_one_mem x hx htN)
    (KfLevelSol.glFin_conj_unipotentGL2_inv_sub_one_mem x hx htN) g⟩

#print axioms solution

end S_AutomorphicForm_IsKfSmooth_exists_ideal_forall_apply_mul_conj_unipotentGL2_eq
end P2MW
export P2MW.S_AutomorphicForm_IsKfSmooth_exists_ideal_forall_apply_mul_conj_unipotentGL2_eq (solution)
