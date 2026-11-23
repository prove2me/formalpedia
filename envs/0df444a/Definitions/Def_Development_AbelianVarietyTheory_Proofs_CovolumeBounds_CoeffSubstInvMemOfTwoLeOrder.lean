-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_CoeffSubstInvMemOfTwoLeOrder
-- name    : Development_AbelianVarietyTheory_Proofs_CovolumeBounds_CoeffSubstInvMemOfTwoLeOrder
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T12:43:54.318436+00:00
-- url     : https://prove2.me/theorems/c059255d-ae32-4ce4-b632-6c13d8f33905
-- title:
--   Coeff Subst Inv Mem Of Two Le Order
-- statement:
--   Definitions and structural lemmas for Coeff Subst Inv Mem Of Two Le Order, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/CoeffSubstInvMemOfTwoLeOrder.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPowerSeries Finsupp
noncomputable section
namespace GlobalTheory.FormalInv
variable {σ τ υ ι : Type*} {R : Type*} [CommRing R]
def weightGe (w : σ → ℕ) (n : ℕ) : Ideal (MvPowerSeries σ R) where
  carrier := {f | ∀ d, weight w d < n → coeff d f = 0}
  add_mem' hf hg d hd := by simp [hf d hd, hg d hd]
  zero_mem' d _ := by simp
  smul_mem' c f hf d hd := by
    classical
    rw [smul_eq_mul, coeff_mul]
    refine Finset.sum_eq_zero fun p hp => ?_
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
    rw [hf p.2 (by rw [← hp, map_add] at hd; omega), mul_zero]
theorem mem_weightGe {w : σ → ℕ} {n : ℕ} {f : MvPowerSeries σ R} :
    f ∈ weightGe w n ↔ ∀ d, weight w d < n → coeff d f = 0 := Iff.rfl
theorem mem_weightGe_iff_le_weightedOrder {w : σ → ℕ} {n : ℕ} {f : MvPowerSeries σ R} :
    f ∈ weightGe w n ↔ (n : ℕ∞) ≤ f.weightedOrder w :=
  ⟨fun h => nat_le_weightedOrder w h, fun h d hd =>
    coeff_eq_zero_of_lt_weightedOrder w (lt_of_lt_of_le (by exact_mod_cast hd) h)⟩
theorem weightGe_mono {w : σ → ℕ} {m n : ℕ} (h : m ≤ n) {f : MvPowerSeries σ R}
    (hf : f ∈ weightGe w n) : f ∈ weightGe w m := fun d hd => hf d (hd.trans_le h)
theorem mem_weightGe_zero {w : σ → ℕ} (f : MvPowerSeries σ R) : f ∈ weightGe w 0 :=
  fun _ hd => absurd hd (Nat.not_lt_zero _)
theorem mul_mem_weightGe {w : σ → ℕ} {m n : ℕ} {f g : MvPowerSeries σ R}
    (hf : f ∈ weightGe w m) (hg : g ∈ weightGe w n) : f * g ∈ weightGe w (m + n) := by
  rw [mem_weightGe_iff_le_weightedOrder] at *
  push_cast
  exact (add_le_add hf hg).trans (le_weightedOrder_mul w)
theorem smul_mem_weightGe {w : σ → ℕ} {n : ℕ} (r : R) {f : MvPowerSeries σ R}
    (hf : f ∈ weightGe w n) : r • f ∈ weightGe w n := fun d hd => by simp [hf d hd]
theorem prod_pow_mem_weightGe {w : τ → ℕ} {w' : σ → ℕ} {a : σ → MvPowerSeries τ R}
    (ha : ∀ s, a s ∈ weightGe w (w' s)) (d : σ →₀ ℕ) :
    (d.prod fun s e => a s ^ e) ∈ weightGe w (weight w' d) := by
  classical
  induction d using Finsupp.induction_linear with
  | zero => simpa using mem_weightGe_zero _
  | add f g hf hg =>
    rw [Finsupp.prod_add_index' (by simp) (by simp [pow_add]), map_add]
    exact mul_mem_weightGe hf hg
  | single s n =>
    rw [Finsupp.prod_single_index (by simp), weight_single]
    induction n with
    | zero => simpa using mem_weightGe_zero _
    | succ n ih =>
      rw [pow_succ, add_smul, one_smul]
      exact mul_mem_weightGe ih (ha s)
abbrev degGe (σ : Type*) (R : Type*) [CommRing R] (n : ℕ) : Ideal (MvPowerSeries σ R) :=
  weightGe (fun _ => 1) n
theorem mem_degGe {n : ℕ} {f : MvPowerSeries σ R} :
    f ∈ degGe σ R n ↔ ∀ d : σ →₀ ℕ, d.degree < n → coeff d f = 0 := by
  simp only [mem_weightGe, degree_eq_weight_one]
theorem mem_degGe_iff_le_order {n : ℕ} {f : MvPowerSeries σ R} :
    f ∈ degGe σ R n ↔ (n : ℕ∞) ≤ f.order := mem_weightGe_iff_le_weightedOrder
theorem mem_degGe_one {f : MvPowerSeries σ R} : f ∈ degGe σ R 1 ↔ constantCoeff f = 0 := by
  rw [mem_degGe_iff_le_order]; exact one_le_order_iff_constCoeff_eq_zero
theorem eq_of_forall_sub_mem_degGe {f g : MvPowerSeries σ R}
    (h : ∀ n, f - g ∈ degGe σ R n) : f = g := by
  ext d
  have := mem_degGe.1 (h (d.degree + 1)) d (Nat.lt_succ_self _)
  rwa [map_sub, sub_eq_zero] at this
theorem prod_pow_sub_mem_degGe {a b : σ → MvPowerSeries τ R} {k : ℕ}
    (ha : ∀ s, a s ∈ degGe τ R 1) (hb : ∀ s, b s ∈ degGe τ R 1)
    (hab : ∀ s, a s - b s ∈ degGe τ R (k + 1)) (d : σ →₀ ℕ) :
    (d.prod fun s e => a s ^ e) - (d.prod fun s e => b s ^ e) ∈ degGe τ R (k + d.degree) := by
  classical
  have hd : ∀ d : σ →₀ ℕ, d.degree = weight (fun _ => 1) d := fun d => by
    rw [degree_eq_weight_one]
  have key : ∀ (m n : ℕ) (p p' q q' : MvPowerSeries τ R), p ∈ degGe τ R m → q' ∈ degGe τ R n →
      p - p' ∈ degGe τ R (k + m) → q - q' ∈ degGe τ R (k + n) →
      p * q - p' * q' ∈ degGe τ R (k + (m + n)) := by
    intro m n p p' q q' h1 h2 h3 h4
    have : p * q - p' * q' = p * (q - q') + (p - p') * q' := by ring
    rw [this]
    refine Ideal.add_mem _ ?_ ?_
    · exact weightGe_mono (by omega) (mul_mem_weightGe h1 h4)
    · exact weightGe_mono (by omega) (mul_mem_weightGe h3 h2)
  induction d using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg =>
    rw [Finsupp.prod_add_index' (by simp) (by simp [pow_add]),
      Finsupp.prod_add_index' (by simp) (by simp [pow_add]), map_add]
    refine key _ _ _ _ _ _ ?_ ?_ hf hg
    · rw [hd]; exact prod_pow_mem_weightGe ha f
    · rw [hd]; exact prod_pow_mem_weightGe hb g
  | single s n =>
    rw [Finsupp.prod_single_index (by simp), Finsupp.prod_single_index (by simp), degree_single]
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ, pow_succ]
      refine key _ _ _ _ _ _ ?_ (hb s) ih (hab s)
      have := prod_pow_mem_weightGe ha (single s n)
      rwa [Finsupp.prod_single_index (by simp), ← hd, degree_single] at this
theorem subst_sub_subst_mem_degGe [Finite σ] {a b : σ → MvPowerSeries τ R} {k m : ℕ}
    (ha : ∀ s, a s ∈ degGe τ R 1) (hb : ∀ s, b s ∈ degGe τ R 1)
    (hab : ∀ s, a s - b s ∈ degGe τ R (k + 1)) {f : MvPowerSeries σ R} (hf : f ∈ degGe σ R m) :
    f.subst a - f.subst b ∈ degGe τ R (k + m) := by
  have ha' : HasSubst a := hasSubst_of_constantCoeff_zero fun s => mem_degGe_one.1 (ha s)
  have hb' : HasSubst b := hasSubst_of_constantCoeff_zero fun s => mem_degGe_one.1 (hb s)
  rw [mem_degGe]
  intro e he
  rw [map_sub, sub_eq_zero, coeff_subst ha', coeff_subst hb']
  refine finsum_congr fun d => ?_
  by_cases hd : d.degree < m
  · simp [mem_degGe.1 hf d hd]
  · have := mem_degGe.1 (prod_pow_sub_mem_degGe ha hb hab d) e (by omega)
    rw [map_sub, sub_eq_zero] at this
    rw [this]
theorem subst_mem_weightGe {w : τ → ℕ} {w' : σ → ℕ} {a : σ → MvPowerSeries τ R}
    (ha' : HasSubst a) (ha : ∀ s, a s ∈ weightGe w (w' s)) {m : ℕ} {f : MvPowerSeries σ R}
    (hf : f ∈ weightGe w' m) : f.subst a ∈ weightGe w m := by
  intro e he
  rw [coeff_subst ha']
  refine finsum_eq_zero_of_forall_eq_zero fun d => ?_
  by_cases hd : weight w' d < m
  · simp [hf d hd]
  · simp [prod_pow_mem_weightGe ha d e (by omega)]
def coeffsIn {κ : Type*} (S : Subring R) (w : κ → σ → ℕ) (g : κ → ℕ) :
    Subring (MvPowerSeries σ R) where
  carrier := {f | ∀ d, (∀ k, weight (w k) d < g k) → coeff d f ∈ S}
  add_mem' hf hg d hd := by rw [map_add]; exact S.add_mem (hf d hd) (hg d hd)
  zero_mem' d _ := by simp
  neg_mem' hf d hd := by rw [map_neg]; exact S.neg_mem (hf d hd)
  one_mem' d _ := by
    classical
    rw [coeff_one]; split_ifs <;> simp
  mul_mem' {f f'} hf hf' d hd := by
    classical
    rw [coeff_mul]
    refine S.sum_mem fun p hp => ?_
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
    refine S.mul_mem (hf _ fun k => ?_) (hf' _ fun k => ?_) <;>
    · have := hd k
      rw [← hp, map_add] at this
      omega
abbrev coeffsInDeg (σ : Type*) (S : Subring R) (g : ℕ) : Subring (MvPowerSeries σ R) :=
  coeffsIn S (fun (_ : Unit) _ => 1) (fun _ => g)
def linearPart (u : ι → MvPowerSeries σ R) : Matrix ι σ R :=
  Matrix.of fun i j => coeff (single j 1) (u i)
@[simp] theorem linearPart_apply (u : ι → MvPowerSeries σ R) (i : ι) (j : σ) :
    linearPart u i j = coeff (single j 1) (u i) := rfl
theorem linearPart_X [DecidableEq σ] : linearPart (X : σ → MvPowerSeries σ R) = 1 := by
  ext i j
  simp [coeff_X, Matrix.one_apply, Finsupp.single_left_inj, eq_comm]
theorem mem_degGe_two {f : MvPowerSeries σ R} :
    f ∈ degGe σ R 2 ↔ constantCoeff f = 0 ∧ ∀ j, coeff (single j 1) f = 0 := by
  rw [mem_degGe]
  refine ⟨fun h => ⟨h 0 (by simp), fun j => h _ (by simp)⟩, fun h d hd => ?_⟩
  rcases (by omega : d.degree = 0 ∨ d.degree = 1) with h0 | h1
  · obtain rfl := (Finsupp.degree_eq_zero_iff d).1 h0
    exact h.1
  · have : d ∈ Set.range fun a : σ => single a 1 := by rw [Finsupp.range_single_one]; exact h1
    obtain ⟨j, rfl⟩ := this
    exact h.2 j
def higherPart [Fintype σ] (u : ι → MvPowerSeries σ R) (i : ι) : MvPowerSeries σ R :=
  u i - ∑ j, linearPart u i j • X j
theorem higherPart_mem_degGe [Fintype σ] {u : ι → MvPowerSeries σ R} {i : ι}
    (hu : constantCoeff (u i) = 0) : higherPart u i ∈ degGe σ R 2 := by
  classical
  rw [mem_degGe_two]
  refine ⟨by simp [higherPart, hu], fun j => ?_⟩
  simp [higherPart, coeff_X, Finsupp.single_left_inj]
theorem subst_eq_linearPart_add [Fintype σ] (u : ι → MvPowerSeries σ R) (i : ι)
    {v : σ → MvPowerSeries τ R} (hv : HasSubst v) :
    (u i).subst v = ∑ j, linearPart u i j • v j + (higherPart u i).subst v := by
  rw [higherPart, ← coe_substAlgHom hv, map_sub, map_sum]
  simp [subst_X hv]
theorem linearPart_subst [Fintype σ] {u : ι → MvPowerSeries σ R} {v : σ → MvPowerSeries τ R}
    (hu : ∀ i, constantCoeff (u i) = 0) (hv : ∀ j, constantCoeff (v j) = 0) :
    linearPart (fun i => (u i).subst v) = linearPart u * linearPart v := by
  ext i l
  have hv' := hasSubst_of_constantCoeff_zero hv
  have := (mem_degGe_two.1 (subst_mem_weightGe hv' (fun s => mem_degGe_one.2 (hv s))
    (higherPart_mem_degGe (hu i)))).2 l
  rw [linearPart_apply, subst_eq_linearPart_add u i hv', map_add, this]
  simp [Matrix.mul_apply]
section Approx
variable [Fintype σ] [Fintype τ] (u : σ → MvPowerSeries τ R) (B : Matrix τ σ R)
def approxStep (v : τ → MvPowerSeries σ R) (j : τ) : MvPowerSeries σ R :=
  ∑ i, B j i • (X i - (higherPart u i).subst v)
def approxLimit (j : τ) : MvPowerSeries σ R :=
  fun d => coeff d (((approxStep u B)^[d.degree + 1] 0) j)
variable {u} {B}
theorem coeff_approxLimit (j : τ) (d : σ →₀ ℕ) :
    coeff d (approxLimit u B j) = coeff d (((approxStep u B)^[d.degree + 1] 0) j) := rfl
theorem approxStep_mem_degGe (hu : ∀ i, constantCoeff (u i) = 0) {v : τ → MvPowerSeries σ R}
    (hv : ∀ j, v j ∈ degGe σ R 1) (j : τ) : approxStep u B v j ∈ degGe σ R 1 := by
  refine Ideal.sum_mem _ fun i _ => smul_mem_weightGe _ (Ideal.sub_mem _ ?_ ?_)
  · exact mem_degGe_one.2 (by simp)
  · exact weightGe_mono (by omega) (subst_mem_weightGe
      (hasSubst_of_constantCoeff_zero fun s => mem_degGe_one.1 (hv s)) hv
      (higherPart_mem_degGe (hu i)))
theorem approxStep_sub_mem_degGe (hu : ∀ i, constantCoeff (u i) = 0)
    {v v' : τ → MvPowerSeries σ R} (hv : ∀ j, v j ∈ degGe σ R 1) (hv' : ∀ j, v' j ∈ degGe σ R 1)
    {k : ℕ} (h : ∀ j, v j - v' j ∈ degGe σ R (k + 1)) (j : τ) :
    approxStep u B v j - approxStep u B v' j ∈ degGe σ R (k + 2) := by
  rw [approxStep, approxStep, ← Finset.sum_sub_distrib]
  refine Ideal.sum_mem _ fun i _ => ?_
  rw [← smul_sub, sub_sub_sub_cancel_left, ← neg_sub]
  exact smul_mem_weightGe _ (Submodule.neg_mem _
    (subst_sub_subst_mem_degGe hv hv' h (higherPart_mem_degGe (hu i))))
theorem iterate_mem_degGe (hu : ∀ i, constantCoeff (u i) = 0) (n : ℕ) (j : τ) :
    ((approxStep u B)^[n] 0) j ∈ degGe σ R 1 := by
  induction n generalizing j with
  | zero => simp
  | succ n ih => rw [Function.iterate_succ_apply']; exact approxStep_mem_degGe hu ih j
theorem iterate_sub_mem_degGe (hu : ∀ i, constantCoeff (u i) = 0) (n m : ℕ) (j : τ) :
    ((approxStep u B)^[n + m] 0) j - ((approxStep u B)^[n] 0) j ∈ degGe σ R (n + 1) := by
  induction n generalizing j with
  | zero => simpa using iterate_mem_degGe hu m j
  | succ n ih =>
    rw [show n + 1 + m = (n + m) + 1 by ring, Function.iterate_succ_apply',
      Function.iterate_succ_apply']
    exact approxStep_sub_mem_degGe hu (iterate_mem_degGe hu _) (iterate_mem_degGe hu _) ih j
theorem approxLimit_sub_mem_degGe (hu : ∀ i, constantCoeff (u i) = 0) (n : ℕ) (j : τ) :
    approxLimit u B j - ((approxStep u B)^[n] 0) j ∈ degGe σ R (n + 1) := by
  rw [mem_degGe]
  intro d hd
  rw [map_sub, coeff_approxLimit, ← map_sub]
  rcases le_total (d.degree + 1) n with h | h
  · obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le h
    rw [← neg_sub, map_neg, mem_degGe.1 (iterate_sub_mem_degGe hu _ m j) d (by omega), neg_zero]
  · obtain ⟨m, hm⟩ := Nat.exists_eq_add_of_le h
    rw [hm]
    exact mem_degGe.1 (iterate_sub_mem_degGe hu _ m j) d hd
theorem approxLimit_mem_degGe (hu : ∀ i, constantCoeff (u i) = 0) (j : τ) :
    approxLimit u B j ∈ degGe σ R 1 := by
  simpa using approxLimit_sub_mem_degGe (B := B) hu 0 j
theorem approxStep_approxLimit (hu : ∀ i, constantCoeff (u i) = 0) (j : τ) :
    approxStep u B (approxLimit u B) j = approxLimit u B j := by
  refine eq_of_forall_sub_mem_degGe fun n => ?_
  have h1 := approxStep_sub_mem_degGe (B := B) hu (approxLimit_mem_degGe (B := B) hu)
    (iterate_mem_degGe (B := B) hu n) (approxLimit_sub_mem_degGe hu n) j
  have h2 := approxLimit_sub_mem_degGe (B := B) hu (n + 1) j
  rw [Function.iterate_succ_apply'] at h2
  have := Ideal.sub_mem _ h1 h2
  rw [sub_sub_sub_cancel_right] at this
  exact weightGe_mono (by omega) this
theorem subst_approxLimit [DecidableEq σ] (hu : ∀ i, constantCoeff (u i) = 0)
    (hB : linearPart u * B = 1) (i : σ) : (u i).subst (approxLimit u B) = X i := by
  have hv : HasSubst (approxLimit u B) :=
    hasSubst_of_constantCoeff_zero fun s => mem_degGe_one.1 (approxLimit_mem_degGe hu s)
  rw [subst_eq_linearPart_add u i hv]
  have : ∑ j, linearPart u i j • approxLimit u B j =
      ∑ l, (linearPart u * B) i l • (X l - (higherPart u l).subst (approxLimit u B)) := by
    simp_rw [Matrix.mul_apply, Finset.sum_smul, mul_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← Finset.smul_sum, ← approxStep_approxLimit hu j]
    rfl
  rw [this, hB]
  simp [Matrix.one_apply]
end Approx
theorem eq_of_subst_eq_X [Finite σ] [Finite τ] {u w : σ → MvPowerSeries τ R}
    {v : τ → MvPowerSeries σ R} (hv : ∀ j, constantCoeff (v j) = 0)
    (hw : ∀ i, constantCoeff (w i) = 0)
    (huv : ∀ i, (u i).subst v = X i) (hvw : ∀ j, (v j).subst w = X j) : u = w := by
  have hv' := hasSubst_of_constantCoeff_zero hv
  have hw' := hasSubst_of_constantCoeff_zero hw
  funext i
  have := subst_comp_subst_apply hv' hw' (u i)
  rw [huv, subst_X hw', funext hvw] at this
  rw [this]
  exact (congrFun subst_self (u i)).symm
section Inverse
variable [Fintype σ] [DecidableEq σ]
def substInv (u : σ → MvPowerSeries σ R) : σ → MvPowerSeries σ R :=
  approxLimit u (linearPart u)⁻¹
variable {u v : σ → MvPowerSeries σ R}
theorem constantCoeff_substInv (hu : ∀ i, constantCoeff (u i) = 0) (i : σ) :
    constantCoeff (substInv u i) = 0 :=
  mem_degGe_one.1 (approxLimit_mem_degGe hu i)
theorem hasSubst_substInv (hu : ∀ i, constantCoeff (u i) = 0) : HasSubst (substInv u) :=
  hasSubst_of_constantCoeff_zero (constantCoeff_substInv hu)
theorem subst_substInv_right (hu : ∀ i, constantCoeff (u i) = 0) (hA : IsUnit (linearPart u))
    (i : σ) : (u i).subst (substInv u) = X i :=
  subst_approxLimit hu (Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 hA)) i
theorem linearPart_mul_eq_one (hu : ∀ i, constantCoeff (u i) = 0)
    (hv : ∀ i, constantCoeff (v i) = 0) (h : ∀ i, (u i).subst v = X i) :
    linearPart u * linearPart v = 1 := by
  rw [← linearPart_subst hu hv, funext h]
  exact linearPart_X
theorem isUnit_linearPart_substInv (hu : ∀ i, constantCoeff (u i) = 0)
    (hA : IsUnit (linearPart u)) : IsUnit (linearPart (substInv u)) :=
  IsUnit.of_mul_eq_one_right _ (linearPart_mul_eq_one hu (constantCoeff_substInv hu)
    (subst_substInv_right hu hA))
theorem substInv_substInv (hu : ∀ i, constantCoeff (u i) = 0) (hA : IsUnit (linearPart u)) :
    substInv (substInv u) = u :=
  (eq_of_subst_eq_X (constantCoeff_substInv hu)
    (constantCoeff_substInv (constantCoeff_substInv hu)) (subst_substInv_right hu hA)
    (subst_substInv_right (constantCoeff_substInv hu) (isUnit_linearPart_substInv hu hA))).symm
theorem subst_substInv_left (hu : ∀ i, constantCoeff (u i) = 0) (hA : IsUnit (linearPart u))
    (i : σ) : (substInv u i).subst u = X i := by
  have := subst_substInv_right (constantCoeff_substInv hu) (isUnit_linearPart_substInv hu hA) i
  rwa [substInv_substInv hu hA] at this
theorem subst_substInv_subst (hu : ∀ i, constantCoeff (u i) = 0) (hA : IsUnit (linearPart u))
    (f : MvPowerSeries σ R) : (f.subst u).subst (substInv u) = f := by
  rw [subst_comp_subst_apply (hasSubst_of_constantCoeff_zero hu) (hasSubst_substInv hu),
    funext (subst_substInv_right hu hA)]
  exact congrFun subst_self f
theorem subst_subst_substInv (hu : ∀ i, constantCoeff (u i) = 0) (hA : IsUnit (linearPart u))
    (f : MvPowerSeries σ R) : (f.subst (substInv u)).subst u = f := by
  rw [subst_comp_subst_apply (hasSubst_substInv hu) (hasSubst_of_constantCoeff_zero hu),
    funext (subst_substInv_left hu hA)]
  exact congrFun subst_self f
def substAlgEquiv (hu : ∀ i, constantCoeff (u i) = 0) (hA : IsUnit (linearPart u)) :
    MvPowerSeries σ R ≃ₐ[R] MvPowerSeries σ R :=
  AlgEquiv.ofAlgHom (substAlgHom (hasSubst_of_constantCoeff_zero hu))
    (substAlgHom (hasSubst_substInv hu))
    (AlgHom.ext fun f => by simp [subst_subst_substInv hu hA])
    (AlgHom.ext fun f => by simp [subst_substInv_subst hu hA])
end Inverse
section TwoGroups
variable {σ' τ' : Type*}
def sumFamily [Finite τ] [Finite τ'] (a : σ → MvPowerSeries τ R) (a' : σ' → MvPowerSeries τ' R) :
    σ ⊕ σ' → MvPowerSeries (τ ⊕ τ') R :=
  Sum.elim (fun i => rename Sum.inl (a i)) (fun j => rename Sum.inr (a' j))
def groupWeight (σ σ' : Type*) : Bool → σ ⊕ σ' → ℕ
  | true => Sum.elim (fun _ => 1) (fun _ => 0)
  | false => Sum.elim (fun _ => 0) (fun _ => 1)
end TwoGroups
end GlobalTheory.FormalInv


