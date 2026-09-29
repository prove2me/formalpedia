-- Prove2me | solution 1 for AutomorphicForm.apply_mul_mul_eq_of_forall_mem_levelOne_of_valued_sub_one_le_of_valued_apply_le
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/a16cfcb4-0122-5031-974e-77564c1ffb92

import Definitions.Def_AutomorphicForm_ArchDerivCasimir
import Definitions.Def_NumberField_AdelicLevel
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_apply_mul_mul_eq_of_forall_mem_levelOne_of_valued_sub_one_le_of_valued_apply_le

set_option autoImplicit false

open NumberField NumberField.AdelicLevel IsDedekindDomain AutomorphicForm

namespace RS37S

variable (K : Type) [Field K] [NumberField K]

theorem mem_levelOne_inf_of_cong (N : Ideal (𝓞 K)) (hN : N ≠ ⊥) (S : Finset (HeightOneSpectrum (𝓞 K))) (n : ℕ)
    (hS : ∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ N → v ∈ S)
    (hn : ∀ v ∈ S, ((Multiplicative.ofAdd (-(n : ℤ)) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) ≤
      idealBound (𝓞 K) N v)
    (k : AdelicGL2 (𝓞 K) K) (hkf : k ∈ finiteAdelicGL2Subgroup K)
    (hki : glFin (𝓞 K) K k ∈ finiteIntegralGL2 (𝓞 K) K)
    (hcong : ∀ v ∈ S, ∀ i j : Fin 2,
      Valued.v ((((k : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i j -
          (1 : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i j)).2 v) ≤
        ((Multiplicative.ofAdd (-(n : ℤ)) : Multiplicative ℤ) : WithZero (Multiplicative ℤ))) :
    k ∈ levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K := by
  set e : WithZero (Multiplicative ℤ) := ((Multiplicative.ofAdd (-(n : ℤ)) : Multiplicative ℤ) : WithZero (Multiplicative ℤ))
    with he
  set A : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 K) K) :=
    ((glFin (𝓞 K) K k : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K)) : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 K) K))
    with hAdef
  set B : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 K) K) :=
    (((glFin (𝓞 K) K k)⁻¹ : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K)) : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 K) K))
    with hBdef
  obtain ⟨hint, hint'⟩ := (mem_finiteIntegralGL2_iff).mp hki

  have hA : ∀ v ∈ S, ∀ i j : Fin 2, Valued.v ((A - 1) i j v) ≤ e := by
    intro v hv i j
    have h := hcong v hv i j
    have hij : (A - 1) i j v = (((k : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i j -
        (1 : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i j)).2 v := by
      rw [Matrix.sub_apply, hAdef, glFin_apply, Matrix.one_apply, Matrix.one_apply]
      split_ifs <;> rfl
    rw [hij]; exact h
  have hBA : B * A = 1 := by
    rw [hBdef, hAdef, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hB : ∀ v ∈ S, ∀ i j : Fin 2, Valued.v ((B - 1) i j v) ≤ e := by
    intro v hv i j
    have hB1 : B - 1 = -(B * (A - 1)) := by rw [mul_sub, mul_one, hBA, neg_sub]
    rw [hB1, Matrix.neg_apply, coe_neg_apply, Valuation.map_neg, Matrix.mul_apply, Fin.sum_univ_two,
      coe_add_apply, coe_mul_apply, coe_mul_apply]
    refine (Valuation.map_add _ _ _).trans (max_le ?_ ?_) <;> rw [map_mul]
    · calc Valued.v (B i 0 v) * Valued.v ((A - 1) 0 j v) ≤ 1 * e :=
            mul_le_mul' (valued_apply_le_one (hint' i 0) v) (hA v hv 0 j)
        _ = e := one_mul e
    · calc Valued.v (B i 1 v) * Valued.v ((A - 1) 1 j v) ≤ 1 * e :=
            mul_le_mul' (valued_apply_le_one (hint' i 1) v) (hA v hv 1 j)
        _ = e := one_mul e

  have hoff : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → idealBound (𝓞 K) N v = 1 :=
    fun v hv => idealBound_eq_one_of_not_dvd hN fun h => hv (hS v h)

  have key : ∀ M : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 K) K),
      (∀ i j, M i j ∈ integralFiniteAdeles (𝓞 K) K) → (∀ v ∈ S, ∀ i j : Fin 2, Valued.v ((M - 1) i j v) ≤ e) →
      IsLevelOneMatrix (𝓞 K) K N M := by
    intro M hM hMc
    refine ⟨⟨hM, fun v => ?_⟩, fun v => ?_⟩
    · by_cases hv : v ∈ S
      · have h := hMc v hv 1 0
        rw [Matrix.sub_apply, Matrix.one_apply_ne (by decide), sub_zero] at h
        exact h.trans (hn v hv)
      · rw [hoff v hv]; exact valued_apply_le_one (hM 1 0) v
    · by_cases hv : v ∈ S
      · have h := hMc v hv 1 1
        rw [Matrix.sub_apply, Matrix.one_apply_eq] at h
        exact h.trans (hn v hv)
      · rw [hoff v hv]
        exact valued_apply_le_one (sub_mem_integralFiniteAdeles (hM 1 1) one_mem_integralFiniteAdeles) v
  exact Subgroup.mem_inf.mpr
    ⟨mem_levelOne_iff.mpr (mem_finiteLevelOne_iff.mpr ⟨key A hint hA, key B hint' hB⟩), hkf⟩

theorem ofAdd_neg_le_idealBound {N : Ideal (𝓞 K)} (hN : N ≠ ⊥) (v : HeightOneSpectrum (𝓞 K)) (n : ℕ)
    (h : (Associates.mk v.asIdeal).count (Associates.mk N).factors ≤ n) :
    ((Multiplicative.ofAdd (-(n : ℤ)) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) ≤ idealBound (𝓞 K) N v := by
  rw [idealBound_of_ne_bot hN]
  show WithZero.exp (-(n : ℤ)) ≤ WithZero.exp _
  rw [WithZero.exp_le_exp]
  omega

section Local

variable {L Γ₀ : Type*} [Field L] [LinearOrderedCommGroupWithZero Γ₀] (val : Valuation L Γ₀)

theorem val_conj_sub_one_apply_le (A Ai Q : Matrix (Fin 2) (Fin 2) L) (hAi : Ai * A = 1) (x y : Γ₀)
    (hA : ∀ i j, val (A i j) ≤ x) (hAi' : ∀ i j, val (Ai i j) ≤ x) (hQ : ∀ i j, val ((Q - 1) i j) ≤ y) :
    ∀ i j, val ((Ai * Q * A - 1) i j) ≤ x * y * x := by
  intro i j
  have h1 : Ai * Q * A - 1 = Ai * (Q - 1) * A := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hAi]
  have hterm : ∀ l m, val (Ai i l * (Q - 1) l m * A m j) ≤ x * y * x := fun l m => by
    rw [map_mul, map_mul]
    exact mul_le_mul' (mul_le_mul' (hAi' i l) (hQ l m)) (hA m j)
  rw [h1, Matrix.mul_apply, Fin.sum_univ_two, Matrix.mul_apply, Matrix.mul_apply, Fin.sum_univ_two,
    Fin.sum_univ_two, add_mul, add_mul]
  exact (val.map_add _ _).trans (max_le ((val.map_add _ _).trans (max_le (hterm 0 0) (hterm 1 0)))
    ((val.map_add _ _).trans (max_le (hterm 0 1) (hterm 1 1))))

theorem val_inv_sub_one_apply_le (Q Qi : Matrix (Fin 2) (Fin 2) L) (hQi : Qi * Q = 1) (y : Γ₀)
    (hQi' : ∀ i j, val (Qi i j) ≤ 1) (hQ : ∀ i j, val ((Q - 1) i j) ≤ y) :
    ∀ i j, val ((Qi - 1) i j) ≤ y := by
  intro i j
  have h1 : Qi - 1 = -(Qi * (Q - 1)) := by rw [Matrix.mul_sub, Matrix.mul_one, hQi, neg_sub]
  have hterm : ∀ l, val (Qi i l * (Q - 1) l j) ≤ y := fun l => by
    rw [map_mul]
    calc val (Qi i l) * val ((Q - 1) l j) ≤ 1 * y := mul_le_mul' (hQi' i l) (hQ l j)
      _ = y := one_mul y
  rw [h1, Matrix.neg_apply, Valuation.map_neg, Matrix.mul_apply, Fin.sum_univ_two]
  exact (val.map_add _ _).trans (max_le (hterm 0) (hterm 1))

theorem val_apply_le_one_of_sub_one (Q : Matrix (Fin 2) (Fin 2) L) (y : Γ₀) (hy : y ≤ 1)
    (hQ : ∀ i j, val ((Q - 1) i j) ≤ y) : ∀ i j, val (Q i j) ≤ 1 := by
  intro i j
  have h1 : Q i j = (Q - 1) i j + (1 : Matrix (Fin 2) (Fin 2) L) i j := by
    rw [Matrix.sub_apply, sub_add_cancel]
  rw [h1]
  refine (val.map_add _ _).trans (max_le ((hQ i j).trans hy) ?_)
  rw [Matrix.one_apply]
  split_ifs
  · exact le_of_eq val.map_one
  · exact le_of_eq_of_le val.map_zero zero_le'

end Local

variable (K : Type) [Field K] [NumberField K]

theorem conj_cong (S : Finset (HeightOneSpectrum (𝓞 K))) (a : AdelicGL2 (𝓞 K) K) (c : ℕ)
    (ha : ∀ v ∈ S, ∀ i j : Fin 2,
      Valued.v ((((a : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i j)).2 v) ≤
        ((Multiplicative.ofAdd (c : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) ∧
      Valued.v (((((a⁻¹ : AdelicGL2 (𝓞 K) K) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i j)).2 v) ≤
        ((Multiplicative.ofAdd (c : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)))
    (n₀ : ℕ) (k : AdelicGL2 (𝓞 K) K) (hka : k ∈ finiteAdelicGL2Subgroup K)
    (hki : glFin (𝓞 K) K k ∈ finiteIntegralGL2 (𝓞 K) K)
    (hks : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → finComponent (𝓞 K) K v (glFin (𝓞 K) K k) = 1)
    (hkc : ∀ v ∈ S, ∀ i j : Fin 2,
      Valued.v ((((k : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i j -
          (1 : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i j)).2 v) ≤
        ((Multiplicative.ofAdd (-((n₀ + 2 * c : ℕ) : ℤ)) : Multiplicative ℤ) : WithZero (Multiplicative ℤ))) :
    a⁻¹ * k * a ∈ finiteAdelicGL2Subgroup K ∧
    glFin (𝓞 K) K (a⁻¹ * k * a) ∈ finiteIntegralGL2 (𝓞 K) K ∧
    (∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → finComponent (𝓞 K) K v (glFin (𝓞 K) K (a⁻¹ * k * a)) = 1) ∧
    (∀ v ∈ S, ∀ i j : Fin 2,
      Valued.v (((((a⁻¹ * k * a : AdelicGL2 (𝓞 K) K) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i j -
          (1 : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i j)).2 v) ≤
        ((Multiplicative.ofAdd (-(n₀ : ℤ)) : Multiplicative ℤ) : WithZero (Multiplicative ℤ))) := by

  set F : (v : HeightOneSpectrum (𝓞 K)) → AdelicGL2 (𝓞 K) K →* GL (Fin 2) (v.adicCompletion K) :=
    fun v => (finComponent (𝓞 K) K v).comp (glFin (𝓞 K) K) with hFdef
  have hF : ∀ (v : HeightOneSpectrum (𝓞 K)) (g : AdelicGL2 (𝓞 K) K) (i j : Fin 2),
      ((F v g : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) i j =
        (((g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i j)).2 v := fun _ _ _ _ => rfl
  have hF1 : ∀ (v : HeightOneSpectrum (𝓞 K)) (g : AdelicGL2 (𝓞 K) K) (i j : Fin 2),
      (((F v g : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) - 1) i j =
        (((g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i j -
          (1 : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i j)).2 v := by
    intro v g i j
    rw [Matrix.sub_apply, hF, Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> rfl
  have hconj : ∀ v : HeightOneSpectrum (𝓞 K), F v (a⁻¹ * k * a) = (F v a)⁻¹ * F v k * F v a := fun v => by
    rw [map_mul, map_mul, map_inv]

  set x : WithZero (Multiplicative ℤ) := ((Multiplicative.ofAdd (c : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ))
    with hx
  set y : WithZero (Multiplicative ℤ) :=
    ((Multiplicative.ofAdd (-((n₀ + 2 * c : ℕ) : ℤ)) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) with hy
  set z : WithZero (Multiplicative ℤ) := ((Multiplicative.ofAdd (-(n₀ : ℤ)) : Multiplicative ℤ) : WithZero (Multiplicative ℤ))
    with hz
  have hxyx : x * y * x = z := by
    rw [hx, hy, hz, ← WithZero.coe_mul, ← WithZero.coe_mul, ← ofAdd_add, ← ofAdd_add]
    congr 2
    push_cast
    ring
  have hz1 : z ≤ 1 := by
    rw [hz, ← WithZero.coe_one, WithZero.coe_le_coe, ← ofAdd_zero, Multiplicative.ofAdd_le]
    omega
  have hy1 : y ≤ 1 := by
    rw [hy, ← WithZero.coe_one, WithZero.coe_le_coe, ← ofAdd_zero, Multiplicative.ofAdd_le]
    omega

  have hS : ∀ v ∈ S, (∀ i j : Fin 2, Valued.v
        ((((F v (a⁻¹ * k * a) : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) - 1)
          i j) ≤ z) ∧
      (∀ i j : Fin 2, Valued.v
        (((((F v (a⁻¹ * k * a))⁻¹ : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) - 1)
          i j) ≤ z) := by
    intro v hv
    obtain ⟨hint, hint'⟩ := (mem_finiteIntegralGL2_iff).mp hki
    have hA : ∀ i j : Fin 2, Valued.v (((F v a : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) i j) ≤ x :=
      fun i j => by rw [hF]; exact (ha v hv i j).1
    have hAi : ∀ i j : Fin 2, Valued.v ((((F v a)⁻¹ : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) i j) ≤ x :=
      fun i j => by rw [← map_inv, hF]; exact (ha v hv i j).2
    have hQ : ∀ i j : Fin 2, Valued.v ((((F v k : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) - 1) i j) ≤ y :=
      fun i j => by rw [hF1]; exact hkc v hv i j
    have hQi1 : ∀ i j : Fin 2, Valued.v ((((F v k)⁻¹ : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) i j) ≤ 1 :=
      fun i j => by
        rw [← map_inv, hF]
        exact valued_apply_le_one (hint' i j) v
    have hQi : ∀ i j : Fin 2, Valued.v (((((F v k)⁻¹ : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) - 1) i j) ≤ y :=
      val_inv_sub_one_apply_le Valued.v _ _ (by rw [← Units.val_mul, inv_mul_cancel, Units.val_one]) y hQi1 hQ
    constructor
    · intro i j
      rw [hconj, Units.val_mul, Units.val_mul, ← hxyx]
      exact val_conj_sub_one_apply_le Valued.v _ _ _ (by rw [← Units.val_mul, inv_mul_cancel, Units.val_one])
        x y hA hAi hQ i j
    · intro i j
      rw [hconj, mul_inv_rev, mul_inv_rev, inv_inv, ← mul_assoc, Units.val_mul, Units.val_mul, ← hxyx]
      exact val_conj_sub_one_apply_le Valued.v _ _ _ (by rw [← Units.val_mul, inv_mul_cancel, Units.val_one])
        x y hA hAi hQi i j

  have hoff : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → F v (a⁻¹ * k * a) = 1 := fun v hv => by
    rw [hconj]
    have hk1 : F v k = 1 := hks v hv
    rw [hk1, mul_one, inv_mul_cancel]
  refine ⟨?_, ?_, hoff, fun v hv i j => ?_⟩
  · rw [mem_finiteAdelicGL2Subgroup_iff] at hka ⊢
    rw [map_mul, map_mul, map_inv, hka, mul_one, inv_mul_cancel]
  · rw [mem_finiteIntegralGL2_iff]
    constructor
    · intro i j v
      rw [IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers]
      change Valued.v (((F v (a⁻¹ * k * a) : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) i j) ≤ 1
      by_cases hv : v ∈ S
      · exact val_apply_le_one_of_sub_one Valued.v _ z hz1 (hS v hv).1 i j
      · rw [hoff v hv, Units.val_one, Matrix.one_apply]
        split_ifs
        · exact le_of_eq (map_one _)
        · exact le_of_eq_of_le (map_zero _) zero_le'
    · intro i j v
      rw [IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers]
      change Valued.v ((((F v (a⁻¹ * k * a))⁻¹ : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) i j) ≤ 1
      by_cases hv : v ∈ S
      · exact val_apply_le_one_of_sub_one Valued.v _ z hz1 (hS v hv).2 i j
      · rw [hoff v hv, inv_one, Units.val_one, Matrix.one_apply]
        split_ifs
        · exact le_of_eq (map_one _)
        · exact le_of_eq_of_le (map_zero _) zero_le'
  · rw [← hF1]
    exact (hS v hv).1 i j

end RS37S

theorem solution
    (K : Type) [Field K] [NumberField K] (N : Ideal (𝓞 K)) (hN : N ≠ ⊥) (S : Finset (HeightOneSpectrum (𝓞 K)))
    (hS : ∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ N → v ∈ S)
    (y₀ : AdelicGL2 (𝓞 K) K → ℂ)
    (hy₀lev : ∀ g : AdelicGL2 (𝓞 K) K, ∀ k ∈ levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K, y₀ (g * k) = y₀ g)
    (a : AdelicGL2 (𝓞 K) K) (c : ℕ)
    (ha : ∀ v ∈ S, ∀ i j : Fin 2,
      Valued.v ((((a : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i j)).2 v) ≤
        ((Multiplicative.ofAdd (c : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) ∧
      Valued.v (((((a⁻¹ : AdelicGL2 (𝓞 K) K) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i j)).2 v) ≤
        ((Multiplicative.ofAdd (c : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)))
    (e : ℕ) (he : ∀ v ∈ S, (Associates.mk v.asIdeal).count (Associates.mk N).factors ≤ e)
    (nb : ℕ) (hnb : e + 2 * c ≤ nb) :
    ∀ (g k : AdelicGL2 (𝓞 K) K), k ∈ finiteAdelicGL2Subgroup K →
      glFin (𝓞 K) K k ∈ finiteIntegralGL2 (𝓞 K) K →
      (∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → finComponent (𝓞 K) K v (glFin (𝓞 K) K k) = 1) →
      (∀ v ∈ S, ∀ i j : Fin 2,
        Valued.v ((((k : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i j -
            (1 : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i j)).2 v) ≤
          ((Multiplicative.ofAdd (-(nb : ℤ)) : Multiplicative ℤ) : WithZero (Multiplicative ℤ))) →
      y₀ (g * k * a) = y₀ (g * a) := by
  intro g k hka hki hks hkc
  have hmono : ((Multiplicative.ofAdd (-(nb : ℤ)) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) ≤
      ((Multiplicative.ofAdd (-((e + 2 * c : ℕ) : ℤ)) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) :=
    WithZero.coe_le_coe.mpr (Multiplicative.ofAdd_le.mpr (by omega))
  obtain ⟨h1, h2, -, h4⟩ := RS37S.conj_cong K S a c ha e k hka hki hks (fun v hv i j => (hkc v hv i j).trans hmono)
  have hg : g * k * a = g * a * (a⁻¹ * k * a) := by group
  rw [hg]
  exact hy₀lev (g * a) _ (RS37S.mem_levelOne_inf_of_cong K N hN S e hS
    (fun v hv => RS37S.ofAdd_neg_le_idealBound K hN v e (he v hv)) (a⁻¹ * k * a) h1 h2 h4)

end S_AutomorphicForm_apply_mul_mul_eq_of_forall_mem_levelOne_of_valued_sub_one_le_of_valued_apply_le
end P2MW
export P2MW.S_AutomorphicForm_apply_mul_mul_eq_of_forall_mem_levelOne_of_valued_sub_one_le_of_valued_apply_le (solution)
