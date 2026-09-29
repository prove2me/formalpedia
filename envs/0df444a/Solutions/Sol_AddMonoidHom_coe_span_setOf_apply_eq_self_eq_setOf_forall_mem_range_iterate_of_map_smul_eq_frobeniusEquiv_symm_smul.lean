-- Prove2me | solution 1 for AddMonoidHom.coe_span_setOf_apply_eq_self_eq_setOf_forall_mem_range_iterate_of_map_smul_eq_frobeniusEquiv_symm_smul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/dc540af9-dd45-5742-980c-0bfe56d9f9d0

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AddMonoidHom_coe_span_setOf_apply_eq_self_eq_setOf_forall_mem_range_iterate_of_map_smul_eq_frobeniusEquiv_symm_smul

set_option autoImplicit false

namespace FittingLS

open Module

variable {K : Type*} [Field K] {p : ℕ} [Fact p.Prime] [CharP K p] [PerfectRing K p]
variable {V : Type*} [AddCommGroup V] [Module K V]

section Basic

variable (C : V →+ V) (hC : ∀ (a : K) (v : V), C (a • v) = (frobeniusEquiv K p).symm a • C v)
include hC

theorem iterate_smul (n : ℕ) (a : K) (v : V) :
    (⇑C)^[n] (a • v) = ((⇑(frobeniusEquiv K p).symm)^[n] a) • (⇑C)^[n] v := by
  induction n generalizing a v with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply, Function.iterate_succ_apply, hC, ih]

omit hC in
theorem iterate_add' (n : ℕ) (v w : V) : (⇑C)^[n] (v + w) = (⇑C)^[n] v + (⇑C)^[n] w := by
  induction n generalizing v w with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply, Function.iterate_succ_apply, Function.iterate_succ_apply, map_add, ih]

omit hC in
theorem iterate_zero' (n : ℕ) : (⇑C)^[n] (0 : V) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply, map_zero, ih]

omit hC in
theorem frob_iterate_symm_iterate (n : ℕ) (a : K) :
    ((⇑(frobeniusEquiv K p).symm)^[n] (((⇑(frobeniusEquiv K p))^[n]) a)) = a := by
  induction n generalizing a with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply, ih, (frobeniusEquiv K p).symm_apply_apply]

theorem smul_iterate (n : ℕ) (a : K) (v : V) :
    a • (⇑C)^[n] v = (⇑C)^[n] ((((⇑(frobeniusEquiv K p))^[n]) a) • v) := by
  rw [iterate_smul C hC, frob_iterate_symm_iterate]

def rangeIter (n : ℕ) : Submodule K V where
  carrier := Set.range ((⇑C)^[n])
  add_mem' := by
    rintro _ _ ⟨v, rfl⟩ ⟨w, rfl⟩
    exact ⟨v + w, iterate_add' C n v w⟩
  zero_mem' := ⟨0, iterate_zero' C n⟩
  smul_mem' := by
    rintro a _ ⟨v, rfl⟩
    exact ⟨_, (smul_iterate C hC n a v).symm⟩

theorem mem_rangeIter (n : ℕ) (v : V) : v ∈ rangeIter C hC n ↔ v ∈ Set.range ((⇑C)^[n]) := Iff.rfl

theorem rangeIter_succ_le (n : ℕ) : rangeIter C hC (n + 1) ≤ rangeIter C hC n := by
  rintro _ ⟨v, rfl⟩
  exact ⟨C v, (Function.iterate_succ_apply _ _ _).symm⟩

theorem rangeIter_antitone : Antitone (rangeIter C hC) :=
  antitone_nat_of_succ_le (rangeIter_succ_le C hC)

theorem map_rangeIter (n : ℕ) : (⇑C) '' (rangeIter C hC n : Set V) = rangeIter C hC (n + 1) := by
  ext w
  constructor
  · rintro ⟨_, ⟨v, rfl⟩, rfl⟩
    exact ⟨v, (Function.iterate_succ_apply' _ _ _)⟩
  · rintro ⟨v, rfl⟩
    exact ⟨_, ⟨v, rfl⟩, (Function.iterate_succ_apply' _ _ _).symm⟩

theorem rangeIter_succ_eq_of_eq {n : ℕ} (h : rangeIter C hC (n + 1) = rangeIter C hC n) :
    rangeIter C hC (n + 2) = rangeIter C hC (n + 1) := by
  apply SetLike.coe_injective
  calc ((rangeIter C hC (n + 2) : Submodule K V) : Set V) = (⇑C) '' (rangeIter C hC (n + 1) : Set V) :=
        (map_rangeIter C hC (n + 1)).symm
    _ = (⇑C) '' (rangeIter C hC n : Set V) := by rw [h]
    _ = rangeIter C hC (n + 1) := map_rangeIter C hC n

theorem rangeIter_eq_of_eq {n : ℕ} (h : rangeIter C hC (n + 1) = rangeIter C hC n) :
    ∀ m, n ≤ m → rangeIter C hC m = rangeIter C hC n := by
  intro m hm
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hm
  induction k with
  | zero => rfl
  | succ k ih =>
    have h1 := ih (Nat.le_add_right n k)

    have : ∀ j, rangeIter C hC (n + j + 1) = rangeIter C hC (n + j) := by
      intro j
      induction j with
      | zero => exact h
      | succ j ihj => exact rangeIter_succ_eq_of_eq C hC ihj
    rw [show n + (k + 1) = n + k + 1 by omega, this k, h1]

variable [FiniteDimensional K V]

theorem rangeIter_eq_of_finrank_le (n : ℕ) (hn : finrank K V ≤ n) :
    rangeIter C hC n = rangeIter C hC (finrank K V) := by

  by_contra hne

  have key : ∀ j, (∀ i < j, rangeIter C hC (i + 1) ≠ rangeIter C hC i) → finrank K (rangeIter C hC j) + j ≤ finrank K V := by
    intro j
    induction j with
    | zero =>
      intro _
      simpa using Submodule.finrank_le (rangeIter C hC 0)
    | succ j ih =>
      intro hj
      have h1 := ih (fun i hi => hj i (Nat.lt_succ_of_lt hi))
      have hlt : rangeIter C hC (j + 1) < rangeIter C hC j :=
        lt_of_le_of_ne (rangeIter_succ_le C hC j) (hj j (Nat.lt_succ_self j))
      have := Submodule.finrank_lt_finrank_of_lt hlt
      omega

  by_cases hex : ∃ i, i ≤ finrank K V ∧ rangeIter C hC (i + 1) = rangeIter C hC i
  · obtain ⟨i, hi, heq⟩ := hex
    apply hne
    rw [rangeIter_eq_of_eq C hC heq n (le_trans hi hn), rangeIter_eq_of_eq C hC heq (finrank K V) hi]
  · push Not at hex
    have := key (finrank K V + 1) (fun i hi => hex i (Nat.lt_succ_iff.mp hi))
    omega

theorem rangeIter_finrank_eq_iInf : (rangeIter C hC (finrank K V) : Set V) = {v : V | ∀ m : ℕ, v ∈ Set.range ((⇑C)^[m])} := by
  ext v
  simp only [SetLike.mem_coe, Set.mem_setOf_eq]
  constructor
  · intro hv m
    rcases le_total m (finrank K V) with h | h
    · exact rangeIter_antitone C hC h hv
    · rw [← mem_rangeIter C hC, rangeIter_eq_of_finrank_le C hC m h]; exact hv
  · intro h; exact h _

end Basic

end FittingLS

namespace FittingLS

open Module Polynomial

variable {K : Type*} [Field K] {p : ℕ} [Fact p.Prime] [CharP K p] [PerfectRing K p]

noncomputable abbrev rootHom (K : Type*) [Field K] (p : ℕ) [Fact p.Prime] [CharP K p] [PerfectRing K p] : K →+* K :=
  ((frobeniusEquiv K p).symm : K ≃+* K).toRingHom

scoped instance rootHom_surjective : RingHomSurjective (rootHom K p) := ⟨(frobeniusEquiv K p).symm.surjective⟩

@[scoped simp] theorem rootHom_apply (a : K) : rootHom K p a = (frobeniusEquiv K p).symm a := rfl

section Semilinear

variable {W : Type*} [AddCommGroup W] [Module K W]

def toSL (D : W →+ W) (hD : ∀ (a : K) (w : W), D (a • w) = (frobeniusEquiv K p).symm a • D w) : W →ₛₗ[rootHom K p] W where
  toFun := D
  map_add' := map_add D
  map_smul' := hD

@[scoped simp] theorem toSL_apply (D : W →+ W) (hD : ∀ (a : K) (w : W), D (a • w) = (frobeniusEquiv K p).symm a • D w) (w : W) :
    toSL D hD w = D w := rfl

end Semilinear

section Step1

variable [IsAlgClosed K]
variable {W : Type*} [AddCommGroup W] [Module K W] [FiniteDimensional K W]

theorem fin_succ_eq_snoc {α : Type*} (s : ℕ → α) (n : ℕ) :
    (fun i : Fin (n + 1) => s i) = Fin.snoc (fun i : Fin n => s i) (s n) := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp [Fin.snoc_last]
  · simp [Fin.snoc_castSucc]

theorem exists_ne_zero_apply_eq_self [Nontrivial W] (D : W →+ W) (hD : ∀ (a : K) (w : W), D (a • w) = (frobeniusEquiv K p).symm a • D w)
    (hinj : Function.Injective D) : ∃ w : W, w ≠ 0 ∧ D w = w := by
  classical
  have hp : 1 < p := (Fact.out : p.Prime).one_lt

  have hφF : ∀ z : K, ((frobeniusEquiv K p).symm z) ^ p = z := fun z => by
    rw [← frobenius_def]; exact frobenius_apply_frobeniusEquiv_symm K p z
  have hFφ : ∀ z : K, (frobeniusEquiv K p).symm (z ^ p) = z := fun z => by
    rw [← frobenius_def]; exact (frobeniusEquiv K p).symm_apply_apply z
  have hsmulD : ∀ (b : K) (y : W), b • D y = D ((b ^ p) • y) := fun b y => by rw [hD, hFφ]

  obtain ⟨v, hv⟩ := exists_ne (0 : W)
  let s : ℕ → W := fun i => (⇑D)^[i] v
  have hs0 : s 0 = v := rfl
  have hs_succ : ∀ i, s (i + 1) = D (s i) := fun i => Function.iterate_succ_apply' _ _ _

  have hdep : ∃ m, ¬ LinearIndependent K (fun i : Fin (m + 1) => s i) := by
    refine ⟨finrank K W, fun h => ?_⟩
    have := h.fintype_card_le_finrank
    simp at this
  obtain ⟨m, hm_spec, hmin⟩ : ∃ m, ¬ LinearIndependent K (fun i : Fin (m + 1) => s i) ∧
      ∀ j < m, LinearIndependent K (fun i : Fin (j + 1) => s i) :=
    ⟨Nat.find hdep, Nat.find_spec hdep, fun j hj => not_not.mp (Nat.find_min hdep hj)⟩
  have hLI : LinearIndependent K (fun i : Fin m => s i) := by
    rcases Nat.eq_zero_or_pos m with h0 | hpos
    · subst h0; exact linearIndependent_empty_type
    · obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
      exact hmin k (Nat.lt_succ_self k)
  have hmem : s m ∈ Submodule.span K (Set.range fun i : Fin m => s i) := by
    by_contra h
    exact hm_spec (fin_succ_eq_snoc s m ▸ (linearIndependent_finSnoc.mpr ⟨hLI, h⟩))
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun K).mp hmem

  have hm : 0 < m := by
    rcases Nat.eq_zero_or_pos m with h0 | hpos
    · exfalso
      apply hv
      subst h0
      have h1 : s 0 = 0 := by
        rw [← hc]
        exact Finset.sum_of_isEmpty _
      exact h1
    · exact hpos
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩

  let a : ℕ → K := fun i => if h : i < k + 1 then c ⟨i, h⟩ else 0
  have ha : ∀ i : Fin (k + 1), a i = c i := fun i => by simp only [a, dif_pos i.is_lt]
  have hsum : ∑ i ∈ Finset.range (k + 1), a i • s i = s (k + 1) := by
    rw [← hc, ← Fin.sum_univ_eq_sum_range (fun i => a i • s i) (k + 1)]
    exact Finset.sum_congr rfl (fun i _ => by rw [ha])

  have ha0 : a 0 ≠ 0 := by
    intro h0

    have h1 : s (k + 1) = D (∑ i ∈ Finset.range k, (a (i + 1)) ^ p • s i) := by
      rw [← hsum, Finset.sum_range_succ', h0, zero_smul, add_zero, map_sum]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [hs_succ, hsmulD]
    rw [hs_succ] at h1
    have h2 := hinj h1

    have hLIk := hLI
    rw [fin_succ_eq_snoc s k, linearIndependent_finSnoc] at hLIk
    apply hLIk.2
    rw [h2, ← Fin.sum_univ_eq_sum_range (fun i => (a (i + 1)) ^ p • s i) k]
    exact Submodule.sum_mem _ (fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩))

  let Q : K[X] := X ^ (p ^ (k + 1) - 1) - ∑ i ∈ Finset.range (k + 1), Polynomial.C ((a i) ^ (p ^ (i + 1))) * X ^ (p ^ i - 1)
  have hpm : 2 ≤ p ^ (k + 1) := by
    calc 2 ≤ p := hp
      _ = p ^ 1 := (pow_one p).symm
      _ ≤ p ^ (k + 1) := Nat.pow_le_pow_right (by omega) (Nat.succ_pos k)
  have hQdeg : Q.degree = (p ^ (k + 1) - 1 : ℕ) := by
    show (X ^ (p ^ (k + 1) - 1) - ∑ i ∈ Finset.range (k + 1), Polynomial.C ((a i) ^ (p ^ (i + 1))) * X ^ (p ^ i - 1) : K[X]).degree = _
    rw [degree_sub_eq_left_of_degree_lt, degree_X_pow]
    rw [degree_X_pow]
    refine lt_of_le_of_lt (Polynomial.degree_sum_le _ _) ?_
    rw [Finset.sup_lt_iff (by exact_mod_cast WithBot.bot_lt_coe _)]
    intro i hi
    rw [Finset.mem_range] at hi
    refine lt_of_le_of_lt (Polynomial.degree_C_mul_X_pow_le _ _) ?_
    have : p ^ i < p ^ (k + 1) := Nat.pow_lt_pow_right hp hi
    exact_mod_cast (show p ^ i - 1 < p ^ (k + 1) - 1 by omega)
  have hQ0 : Q.eval 0 ≠ 0 := by
    show (X ^ (p ^ (k + 1) - 1) - ∑ i ∈ Finset.range (k + 1), Polynomial.C ((a i) ^ (p ^ (i + 1))) * X ^ (p ^ i - 1) : K[X]).eval 0 ≠ 0
    rw [eval_sub, eval_pow, eval_X, zero_pow (by omega), zero_sub, neg_ne_zero, eval_finsetSum,
      Finset.sum_range_succ']
    simp only [eval_mul, eval_C, eval_pow, eval_X, pow_zero, Nat.sub_self, pow_zero, mul_one]
    rw [Finset.sum_eq_zero (fun i _ => by
      rw [zero_pow (Nat.sub_ne_zero_of_lt (Nat.one_lt_pow (by omega) hp)), mul_zero]), zero_add]
    exact pow_ne_zero _ ha0
  obtain ⟨y, hy⟩ : ∃ y, Q.IsRoot y := IsAlgClosed.exists_root Q (by rw [hQdeg]; exact_mod_cast (show p ^ (k + 1) - 1 ≠ 0 by omega))
  have hy0 : y ≠ 0 := by rintro rfl; exact hQ0 hy

  have hkey : y ^ (p ^ (k + 1)) = ∑ i ∈ Finset.range (k + 1), (a i) ^ (p ^ (i + 1)) * y ^ (p ^ i) := by
    have h := hy
    simp only [Q, IsRoot.def, eval_sub, eval_pow, eval_X, eval_finsetSum, eval_mul, eval_C, sub_eq_zero] at h
    have h' := congrArg (fun t => y * t) h
    simp only [Finset.mul_sum] at h'
    rw [← pow_succ', Nat.sub_add_cancel (by omega)] at h'
    rw [h']
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [mul_left_comm, ← pow_succ', Nat.sub_add_cancel (Nat.one_le_pow _ _ (by omega))]

  let x : ℕ → K := fun j => Nat.rec ((frobeniusEquiv K p).symm y * a 0)
    (fun j xj => (frobeniusEquiv K p).symm xj + (frobeniusEquiv K p).symm y * a (j + 1)) j
  have hx0 : x 0 = (frobeniusEquiv K p).symm y * a 0 := rfl
  have hx_succ : ∀ j, x (j + 1) = (frobeniusEquiv K p).symm (x j) + (frobeniusEquiv K p).symm y * a (j + 1) := fun j => rfl

  have hpowφ : ∀ (z : K) (n : ℕ), ((frobeniusEquiv K p).symm z) ^ (p ^ (n + 1)) = z ^ (p ^ n) := fun z n => by
    rw [pow_succ', pow_mul, hφF]
  have hdag : ∀ j, (x j) ^ (p ^ (j + 1)) = ∑ i ∈ Finset.range (j + 1), y ^ (p ^ i) * (a i) ^ (p ^ (i + 1)) := by
    intro j
    induction j with
    | zero =>
      rw [hx0, Finset.sum_range_one, mul_pow, hpowφ, pow_zero, pow_one, pow_one]
    | succ j ih =>
      rw [hx_succ, add_pow_char_pow, hpowφ, ih, mul_pow, hpowφ]
      exact (Finset.sum_range_succ _ (j + 1)).symm

  have hxy : x k = y := by
    have h1 : (x k) ^ (p ^ (k + 1)) = y ^ (p ^ (k + 1)) := by
      rw [hdag k, hkey]
      exact Finset.sum_congr rfl (fun i _ => mul_comm _ _)
    have hinjF : Function.Injective (iterateFrobenius K p (k + 1)) := (iterateFrobenius K p (k + 1)).injective
    apply hinjF
    rw [iterateFrobenius_def, iterateFrobenius_def, h1]

  refine ⟨∑ i ∈ Finset.range (k + 1), x i • s i, ?_, ?_⟩
  ·
    intro h0
    rw [← Fin.sum_univ_eq_sum_range (fun i => x i • s i) (k + 1)] at h0
    have := Fintype.linearIndependent_iff.mp hLI (fun i => x i) h0 ⟨k, by omega⟩
    exact hy0 (hxy ▸ this)
  ·
    have eL : D (∑ i ∈ Finset.range (k + 1), x i • s i) =
        ∑ i ∈ Finset.range k, (frobeniusEquiv K p).symm (x i) • s (i + 1) + (frobeniusEquiv K p).symm (x k) • s (k + 1) := by
      rw [map_sum, Finset.sum_range_succ]
      simp_rw [hD, ← hs_succ]
    have eR : ∑ i ∈ Finset.range (k + 1), x i • s i =
        ∑ i ∈ Finset.range k, (frobeniusEquiv K p).symm (x i) • s (i + 1) + (frobeniusEquiv K p).symm y • s (k + 1) := by
      have h1 : (frobeniusEquiv K p).symm y • s (k + 1) =
          ∑ i ∈ Finset.range k, ((frobeniusEquiv K p).symm y * a (i + 1)) • s (i + 1) + ((frobeniusEquiv K p).symm y * a 0) • s 0 := by
        rw [← hsum, Finset.sum_range_succ', smul_add, Finset.smul_sum]
        simp_rw [mul_smul]
      rw [h1, Finset.sum_range_succ', hx0, ← add_assoc, ← Finset.sum_add_distrib]
      congr 1
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [hx_succ, add_smul]
    rw [eL, eR, hxy]

end Step1

section Step2

variable [IsAlgClosed K]

theorem exists_sub_root_eq (a : K) : ∃ x : K, x - (frobeniusEquiv K p).symm x = a := by

  have hp : 1 < p := (Fact.out : p.Prime).one_lt
  have hdeg : (X ^ p - X - Polynomial.C a : K[X]).degree ≠ 0 := by
    have h1 : (X ^ p - X - Polynomial.C a : K[X]).degree = p := by
      rw [sub_sub, degree_sub_eq_left_of_degree_lt] <;> rw [degree_X_pow]
      refine lt_of_le_of_lt (degree_add_le _ _) ?_
      rw [max_lt_iff]
      exact ⟨by rw [degree_X]; exact_mod_cast hp, lt_of_le_of_lt degree_C_le (by exact_mod_cast (Fact.out : p.Prime).pos)⟩
    rw [h1]; exact_mod_cast (Fact.out : p.Prime).ne_zero
  obtain ⟨t, ht⟩ := IsAlgClosed.exists_root _ hdeg
  refine ⟨t ^ p, ?_⟩
  have hfrob : (frobeniusEquiv K p).symm (t ^ p) = t := by
    rw [← frobenius_def]; exact (frobeniusEquiv K p).symm_apply_apply t
  simp only [Polynomial.IsRoot, Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C] at ht
  rw [hfrob]
  linear_combination ht

universe u in

theorem span_fixed_eq_top_aux : ∀ (n : ℕ) (W : Type u) [AddCommGroup W] [Module K W] [FiniteDimensional K W],
    finrank K W = n → ∀ (D : W →+ W), (∀ (a : K) (w : W), D (a • w) = (frobeniusEquiv K p).symm a • D w) →
      Function.Injective D → Submodule.span K {w : W | D w = w} = ⊤ := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro W _ _ _ hn D hD hinj
  rcases subsingleton_or_nontrivial W with hW | hW
  · haveI := hW; exact Subsingleton.elim _ _

  obtain ⟨w₁, hw₁0, hw₁⟩ := exists_ne_zero_apply_eq_self D hD hinj
  let S : Submodule K W := K ∙ w₁
  have hS : S ≤ Submodule.comap (toSL D hD) S := by
    rw [Submodule.span_singleton_le_iff_mem, Submodule.mem_comap, toSL_apply, hw₁]
    exact Submodule.mem_span_singleton_self w₁

  let Dq : W ⧸ S →ₛₗ[rootHom K p] W ⧸ S := Submodule.mapQ S S (toSL D hD) hS
  have hDq_mk : ∀ u : W, Dq (Submodule.Quotient.mk u) = Submodule.Quotient.mk (D u) := fun u => rfl

  have hDq_inj : Function.Injective Dq := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro q hq
    induction q using Submodule.Quotient.induction_on with
    | _ u =>
    rw [LinearMap.mem_ker, hDq_mk, Submodule.Quotient.mk_eq_zero, Submodule.mem_span_singleton] at hq
    obtain ⟨c, hc⟩ := hq
    have : D (frobeniusEquiv K p c • w₁) = D u := by
      rw [hD, (frobeniusEquiv K p).symm_apply_apply, hw₁, hc]
    rw [Submodule.Quotient.mk_eq_zero, ← hinj this]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self w₁)

  have hdim : finrank K (W ⧸ S) < n := by
    have h1 := Submodule.finrank_quotient_add_finrank S
    have h2 : finrank K S = 1 := finrank_span_singleton hw₁0
    omega

  have hIH := ih _ hdim (W ⧸ S) rfl Dq.toAddMonoidHom (fun a q => by
    show Dq (a • q) = _
    rw [LinearMap.map_smulₛₗ]; rfl) hDq_inj

  have hlift : ∀ q : W ⧸ S, Dq q = q → ∃ u : W, D u = u ∧ Submodule.Quotient.mk u = q := by
    intro q hq
    induction q using Submodule.Quotient.induction_on with
    | _ u₀ =>
    rw [hDq_mk, Submodule.Quotient.eq, Submodule.mem_span_singleton] at hq
    obtain ⟨a, ha⟩ := hq

    obtain ⟨x, hx⟩ := exists_sub_root_eq (K := K) (p := p) a
    refine ⟨u₀ + x • w₁, ?_, ?_⟩
    · rw [map_add, hD, hw₁, show D u₀ = u₀ + a • w₁ by rw [ha]; abel, add_assoc, ← add_smul, ← hx]
      congr 1
      ring_nf
    · rw [Submodule.Quotient.mk_add, Submodule.Quotient.mk_smul,
        (Submodule.Quotient.mk_eq_zero S).mpr (Submodule.mem_span_singleton_self w₁), smul_zero, add_zero]

  apply top_unique
  have hF1 : S ≤ Submodule.span K {w : W | D w = w} :=
    (Submodule.span_singleton_le_iff_mem _ _).mpr (Submodule.subset_span hw₁)
  have hmap : Submodule.map S.mkQ (Submodule.span K {w : W | D w = w}) = ⊤ := by
    apply top_unique
    rw [← hIH, Submodule.span_le]
    intro q hq
    obtain ⟨u, hu, rfl⟩ := hlift q hq
    exact ⟨u, Submodule.subset_span hu, rfl⟩
  have := Submodule.comap_map_eq S.mkQ (Submodule.span K {w : W | D w = w})
  rw [hmap, Submodule.comap_top, Submodule.ker_mkQ, sup_eq_left.mpr hF1] at this
  exact this.le

theorem span_setOf_apply_eq_self_eq_top_of_bijective' (K : Type*) [Field K] [IsAlgClosed K] (p : ℕ) [Fact p.Prime] [CharP K p]
    (V : Type*) [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (C : V →+ V) (hC : ∀ (a : K) (v : V), C (a • v) = (frobeniusEquiv K p).symm a • C v)
    (hbij : Function.Bijective C) : Submodule.span K {v : V | C v = v} = ⊤ :=
  span_fixed_eq_top_aux _ V rfl C hC hbij.1

end Step2

end FittingLS
p2m_reactivate "P2MW.S_AddMonoidHom_coe_span_setOf_apply_eq_self_eq_setOf_forall_mem_range_iterate_of_map_smul_eq_frobeniusEquiv_symm_smul.FittingLS"

namespace FittingLS

open Module

variable {K : Type*} [Field K] {p : ℕ} [Fact p.Prime] [CharP K p] [PerfectRing K p]
variable {V : Type*} [AddCommGroup V] [Module K V]

section InjOfSurj

theorem injective_of_surjective {W : Type*} [AddCommGroup W] [Module K W] [FiniteDimensional K W]
    (D : W →+ W) (hD : ∀ (a : K) (w : W), D (a • w) = (frobeniusEquiv K p).symm a • D w)
    (hsurj : Function.Surjective D) : Function.Injective D := by
  classical
  let b := Module.finBasis K W

  have hspan : ⊤ ≤ Submodule.span K (Set.range (fun i => D (b i))) := by
    intro w _
    obtain ⟨v, rfl⟩ := hsurj w
    have hv : v = ∑ i, b.repr v i • b i := (b.sum_repr v).symm
    rw [hv, map_sum]
    refine Submodule.sum_mem _ (fun i _ => ?_)
    rw [hD]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  have hli : LinearIndependent K (fun i => D (b i)) :=
    linearIndependent_of_top_le_span_of_card_eq_finrank hspan (by simp)
  intro v w hvw
  rw [← sub_eq_zero] at hvw ⊢
  rw [← map_sub] at hvw
  set u := v - w with hu
  have hu' : u = ∑ i, b.repr u i • b i := (b.sum_repr u).symm
  rw [hu', map_sum] at hvw
  simp_rw [hD] at hvw
  have h0 := Fintype.linearIndependent_iff.mp hli (fun i => (frobeniusEquiv K p).symm (b.repr u i)) hvw
  rw [hu']
  refine Finset.sum_eq_zero (fun i _ => ?_)
  have : b.repr u i = 0 := by
    have := h0 i
    rwa [map_eq_zero_iff _ (frobeniusEquiv K p).symm.injective] at this
  rw [this, zero_smul]

end InjOfSurj
p2m_reactivate "P2MW.S_AddMonoidHom_coe_span_setOf_apply_eq_self_eq_setOf_forall_mem_range_iterate_of_map_smul_eq_frobeniusEquiv_symm_smul.FittingLS"

section Stable

variable (C : V →+ V) (hC : ∀ (a : K) (v : V), C (a • v) = (frobeniusEquiv K p).symm a • C v)
include hC

omit hC in
theorem map_sum' {ι : Type*} (s : Finset ι) (f : ι → V) : C (∑ i ∈ s, f i) = ∑ i ∈ s, C (f i) := map_sum C f s

variable [FiniteDimensional K V]

noncomputable def stable : Submodule K V := rangeIter C hC (finrank K V)

theorem stable_def : stable C hC = rangeIter C hC (finrank K V) := rfl

theorem apply_mem_stable {v : V} (hv : v ∈ stable C hC) : C v ∈ stable C hC := by
  have h : C v ∈ rangeIter C hC (finrank K V + 1) := by
    rw [← SetLike.mem_coe, ← map_rangeIter C hC]
    exact ⟨v, hv, rfl⟩
  exact rangeIter_succ_le C hC _ h

theorem exists_apply_eq_of_mem_stable {w : V} (hw : w ∈ stable C hC) : ∃ v ∈ stable C hC, C v = w := by
  have h : w ∈ rangeIter C hC (finrank K V + 1) := by
    rw [rangeIter_eq_of_finrank_le C hC _ (Nat.le_succ _)]; exact hw
  rw [← SetLike.mem_coe, ← map_rangeIter C hC] at h
  obtain ⟨v, hv, rfl⟩ := h
  exact ⟨v, hv, rfl⟩

noncomputable def restrict : ↥(stable C hC) →+ ↥(stable C hC) where
  toFun v := ⟨C (v : V), apply_mem_stable C hC v.2⟩
  map_zero' := Subtype.ext (map_zero C)
  map_add' v w := Subtype.ext (map_add C (v : V) (w : V))

@[scoped simp] theorem coe_restrict (v : ↥(stable C hC)) : ((restrict C hC v : ↥(stable C hC)) : V) = C (v : V) := rfl

theorem restrict_smul (a : K) (v : ↥(stable C hC)) : restrict C hC (a • v) = (frobeniusEquiv K p).symm a • restrict C hC v :=
  Subtype.ext (hC a (v : V))

theorem restrict_surjective : Function.Surjective (restrict C hC) := by
  intro w
  obtain ⟨v, hv, hvw⟩ := exists_apply_eq_of_mem_stable C hC w.2
  exact ⟨⟨v, hv⟩, Subtype.ext hvw⟩

theorem restrict_bijective : Function.Bijective (restrict C hC) :=
  ⟨injective_of_surjective (restrict C hC) (restrict_smul C hC) (restrict_surjective C hC), restrict_surjective C hC⟩

end Stable
p2m_reactivate "P2MW.S_AddMonoidHom_coe_span_setOf_apply_eq_self_eq_setOf_forall_mem_range_iterate_of_map_smul_eq_frobeniusEquiv_symm_smul.FittingLS"

section LangSteinberg

theorem span_setOf_apply_eq_self_eq_top_of_bijective (K : Type*) [Field K] [IsAlgClosed K] (p : ℕ) [Fact p.Prime] [CharP K p]
    (V : Type*) [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (C : V →+ V) (hC : ∀ (a : K) (v : V), C (a • v) = (frobeniusEquiv K p).symm a • C v)
    (hbij : Function.Bijective C) : Submodule.span K {v : V | C v = v} = ⊤ :=
  span_setOf_apply_eq_self_eq_top_of_bijective' K p V C hC hbij

end LangSteinberg
p2m_reactivate "P2MW.S_AddMonoidHom_coe_span_setOf_apply_eq_self_eq_setOf_forall_mem_range_iterate_of_map_smul_eq_frobeniusEquiv_symm_smul.FittingLS"

section Main

variable (K : Type*) [Field K] [IsAlgClosed K] (p : ℕ) [Fact p.Prime] [CharP K p]
    (V : Type*) [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (C : V →+ V) (hC : ∀ (a : K) (v : V), C (a • v) = (frobeniusEquiv K p).symm a • C v)
include hC

theorem span_fixed_eq_stable : Submodule.span K {v : V | C v = v} = stable C hC := by
  apply le_antisymm
  · rw [Submodule.span_le]
    intro v hv

    have hfix : ∀ n : ℕ, (⇑C)^[n] v = v := by
      intro n
      induction n with
      | zero => rfl
      | succ n ih => rw [Function.iterate_succ_apply', ih]; exact hv
    exact ⟨v, hfix _⟩
  ·
    intro v hv
    have htop := span_setOf_apply_eq_self_eq_top_of_bijective K p (↥(stable C hC)) (restrict C hC) (restrict_smul C hC)
      (restrict_bijective C hC)
    have hmem : (⟨v, hv⟩ : ↥(stable C hC)) ∈ Submodule.span K {w : ↥(stable C hC) | restrict C hC w = w} := by
      rw [htop]; exact Submodule.mem_top

    have hmap : Submodule.map (stable C hC).subtype (Submodule.span K {w : ↥(stable C hC) | restrict C hC w = w}) ≤
        Submodule.span K {v : V | C v = v} := by
      rw [Submodule.map_span_le]
      rintro w (hw : restrict C hC w = w)
      exact Submodule.subset_span (show C (w : V) = w from congrArg Subtype.val hw)
    exact hmap ⟨⟨v, hv⟩, hmem, rfl⟩

theorem main :
    ((Submodule.span K {v : V | C v = v} : Submodule K V) : Set V) = {v : V | ∀ n : ℕ, v ∈ Set.range ((⇑C)^[n])} ∧
    ∀ n : ℕ, Module.finrank K V ≤ n → Set.range ((⇑C)^[n]) = {v : V | ∀ m : ℕ, v ∈ Set.range ((⇑C)^[m])} := by
  refine ⟨?_, fun n hn => ?_⟩
  · rw [span_fixed_eq_stable K p V C hC, stable_def, rangeIter_finrank_eq_iInf]
  · rw [← rangeIter_finrank_eq_iInf C hC, ← rangeIter_eq_of_finrank_le C hC n hn]
    rfl

end Main
p2m_reactivate "P2MW.S_AddMonoidHom_coe_span_setOf_apply_eq_self_eq_setOf_forall_mem_range_iterate_of_map_smul_eq_frobeniusEquiv_symm_smul.FittingLS"

end FittingLS
p2m_reactivate "P2MW.S_AddMonoidHom_coe_span_setOf_apply_eq_self_eq_setOf_forall_mem_range_iterate_of_map_smul_eq_frobeniusEquiv_symm_smul.FittingLS"

theorem solution
    (K : Type*) [Field K] [IsAlgClosed K] (p : ℕ) [Fact p.Prime] [CharP K p]
    (V : Type*) [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (C : V →+ V) (hC : ∀ (a : K) (v : V), C (a • v) = (frobeniusEquiv K p).symm a • C v) :
    ((Submodule.span K {v : V | C v = v} : Submodule K V) : Set V) = {v : V | ∀ n : ℕ, v ∈ Set.range ((⇑C)^[n])} ∧
    ∀ n : ℕ, Module.finrank K V ≤ n → Set.range ((⇑C)^[n]) = {v : V | ∀ m : ℕ, v ∈ Set.range ((⇑C)^[m])} := by
  exact FittingLS.main K p V C hC

end S_AddMonoidHom_coe_span_setOf_apply_eq_self_eq_setOf_forall_mem_range_iterate_of_map_smul_eq_frobeniusEquiv_symm_smul
end P2MW
export P2MW.S_AddMonoidHom_coe_span_setOf_apply_eq_self_eq_setOf_forall_mem_range_iterate_of_map_smul_eq_frobeniusEquiv_symm_smul (solution)
