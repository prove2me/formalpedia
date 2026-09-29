-- Prove2me | solution 1 for AlgebraicCurve.exists_lift_normalForm_structureConstants_of_smallExtension
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/741293c3-5504-5cf5-9941-1b8140ca059c

import Mathlib
import Theorems.Thm_AlgebraicCurve_exists_local_coboundary_of_smallExtension_of_monogenic_fibre
import Theorems.Thm_AlgebraicCurve_exists_coboundary_at_infinity_of_smallExtension_of_split
import Theorems.Thm_AlgebraicCurve_exists_aeval_sub_mem_smul_of_isMaximal_of_isIntegrallyClosed
import Theorems.Thm_AlgebraicCurve_discr_ne_zero_of_normalForm_split
import Theorems.Thm_AlgebraicCurve_exists_mul_eq_hochschild_coboundary_of_discr_ne_zero
import Theorems.Thm_AlgebraicCurve_exists_bounded_two_cochain_of_local_coboundaries
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_exists_lift_normalForm_structureConstants_of_smallExtension

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open Polynomial

universe u v w w'

noncomputable section

namespace SmallExtSol

section LiftPoly

variable {S T : Type*} [CommRing S] [CommRing T]

def liftPoly (s : T → S) (f : T[X]) : S[X] :=
  ∑ t ∈ Finset.range (f.natDegree + 1), C (s (f.coeff t)) * X ^ t

theorem coeff_liftPoly (s : T → S) (hs0 : s 0 = 0) (f : T[X]) (t : ℕ) :
    (liftPoly s f).coeff t = s (f.coeff t) := by
  rw [liftPoly, finsetSum_coeff]
  simp only [coeff_C_mul_X_pow]
  by_cases ht : t < f.natDegree + 1
  · rw [Finset.sum_eq_single t]
    · rw [if_pos rfl]
    · intro b _ hb; rw [if_neg (Ne.symm hb)]
    · intro h; exact absurd (Finset.mem_range.2 ht) h
  · rw [Finset.sum_eq_zero, coeff_eq_zero_of_natDegree_lt (by omega), hs0]
    intro b hb
    rw [if_neg]
    rintro rfl
    exact ht (Finset.mem_range.1 hb)

theorem map_liftPoly (f' : S →+* T) (s : T → S) (hs0 : s 0 = 0) (hs : ∀ a, f' (s a) = a)
    (f : T[X]) : (liftPoly s f).map f' = f := by
  ext t
  rw [coeff_map, coeff_liftPoly s hs0, hs]

theorem natDegree_liftPoly_le (s : T → S) (hs0 : s 0 = 0) (f : T[X]) :
    (liftPoly s f).natDegree ≤ f.natDegree := by
  rw [natDegree_le_iff_coeff_eq_zero]
  intro t ht
  rw [coeff_liftPoly s hs0, coeff_eq_zero_of_natDegree_lt (by exact_mod_cast ht), hs0]

open Classical in

def sect0 (f' : S →+* T) (hf : Function.Surjective f') : T → S :=
  fun a => if a = 0 then 0 else Function.surjInv hf a

open Classical in
theorem sect0_zero (f' : S →+* T) (hf : Function.Surjective f') : sect0 f' hf 0 = 0 := by
  simp [sect0]

open Classical in
theorem apply_sect0 (f' : S →+* T) (hf : Function.Surjective f') (a : T) :
    f' (sect0 f' hf a) = a := by
  by_cases h : a = 0
  · simp [sect0, h]
  · rw [sect0, if_neg h]; exact Function.surjInv_eq hf a

open Classical in

def divε (ε c : S) : S :=
  if c = 0 then 0 else if h : ε ∣ c then Classical.choose h else 0

open Classical in
theorem divε_zero (ε : S) : divε ε 0 = 0 := by simp [divε]

open Classical in
theorem mul_divε (ε c : S) (h : ε ∣ c) : ε * divε ε c = c := by
  by_cases hc : c = 0
  · simp [divε, hc]
  · rw [divε, if_neg hc, dif_pos h]
    exact (Classical.choose_spec h).symm

def divPoly (ε : S) (g : S[X]) : S[X] :=
  ∑ t ∈ Finset.range (g.natDegree + 1), C (divε ε (g.coeff t)) * X ^ t

theorem coeff_divPoly (ε : S) (g : S[X]) (t : ℕ) : (divPoly ε g).coeff t = divε ε (g.coeff t) := by
  rw [divPoly, finsetSum_coeff]
  simp only [coeff_C_mul_X_pow]
  by_cases ht : t < g.natDegree + 1
  · rw [Finset.sum_eq_single t]
    · rw [if_pos rfl]
    · intro b _ hb; rw [if_neg (Ne.symm hb)]
    · intro h; exact absurd (Finset.mem_range.2 ht) h
  · rw [Finset.sum_eq_zero, coeff_eq_zero_of_natDegree_lt (by omega), divε_zero]
    intro b hb
    rw [if_neg]
    rintro rfl
    exact ht (Finset.mem_range.1 hb)

theorem C_mul_divPoly (ε : S) (g : S[X]) (hg : ∀ t, ε ∣ g.coeff t) : C ε * divPoly ε g = g := by
  ext t
  rw [coeff_C_mul, coeff_divPoly, mul_divε ε _ (hg t)]

theorem natDegree_divPoly_le (ε : S) (g : S[X]) : (divPoly ε g).natDegree ≤ g.natDegree := by
  rw [natDegree_le_iff_coeff_eq_zero]
  intro t ht
  rw [coeff_divPoly, coeff_eq_zero_of_natDegree_lt (by exact_mod_cast ht), divε_zero]

end LiftPoly

section Main

variable {K : Type u} [Field K] [IsAlgClosed K] {n : ℕ} {B : Type v} [CommRing B] [IsDomain B]
  [IsIntegrallyClosed B] [Algebra K[X] B]

theorem repr_mul_unit (e : Module.Basis (Fin (n + 1)) K[X] B) (he : e 0 = 1) (j k : Fin (n + 1)) :
    e.repr (e 0 * e j) k = if j = k then 1 else 0 := by
  rw [he, one_mul, e.repr_self, Finsupp.single_apply]

theorem repr_mul_expand_left (e : Module.Basis (Fin (n + 1)) K[X] B) (i j l m : Fin (n + 1)) :
    e.repr (e i * e j * e l) m = ∑ k, e.repr (e i * e j) k * e.repr (e k * e l) m := by
  conv_lhs => rw [← e.sum_repr (e i * e j), Finset.sum_mul, map_sum]
  rw [Finset.sum_apply']
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [smul_mul_assoc, map_smul, Finsupp.smul_apply, smul_eq_mul]

theorem repr_mul_expand_right (e : Module.Basis (Fin (n + 1)) K[X] B) (i j l m : Fin (n + 1)) :
    e.repr (e i * (e j * e l)) m = ∑ k, e.repr (e j * e l) k * e.repr (e i * e k) m := by
  conv_lhs => rw [← e.sum_repr (e j * e l), Finset.mul_sum, map_sum]
  rw [Finset.sum_apply']
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [mul_smul_comm, map_smul, Finsupp.smul_apply, smul_eq_mul]

theorem repr_mul_assoc (e : Module.Basis (Fin (n + 1)) K[X] B) (i j l m : Fin (n + 1)) :
    ∑ k, e.repr (e i * e j) k * e.repr (e k * e l) m =
      ∑ k, e.repr (e j * e l) k * e.repr (e i * e k) m := by
  rw [← repr_mul_expand_left, ← repr_mul_expand_right, mul_assoc]

theorem main
    (b : Module.Basis (Fin (n + 1)) K[X] B) (d : Fin (n + 1) → ℕ)
    (hb0 : b 0 = 1) (hd0 : d 0 = 0) (hd : ∀ i, i ≠ 0 → d i = 1 ∨ d i = 2)
    (hdeg : ∀ i j k, i ≠ 0 → j ≠ 0 → ((b.repr (b i * b j)) k).natDegree ≤ d i + d j - d k)
    (hinf : ∃ τ : Fin (n + 1) → Fin (n + 1) → K,
      IsUnit (Matrix.det (Matrix.of τ)) ∧
      (∀ j, τ j 0 = 1) ∧
      ∀ j i i', i ≠ 0 → i' ≠ 0 →
        τ j i * τ j i' = ∑ k, ((b.repr (b i * b i')) k).coeff (d i + d i' - d k) * τ j k)
    (A' : Type w) [CommRing A'] (A : Type w') [CommRing A]
    (π : A' →+* A) (hπ : Function.Surjective π) (ε : A') (hker : ∀ a : A', π a = 0 ↔ ε ∣ a)
    (ρ : A →+* K) (hρ : Function.Surjective ρ)
    (hsmall : ∀ a : A', ρ (π a) = 0 → ε * a = 0)
    (hnil : ∀ a : A', ρ (π a) = 0 → IsNilpotent a)
    (γ : Fin (n + 1) → Fin (n + 1) → Fin (n + 1) → A[X])
    (hγ1 : ∀ j k, γ 0 j k = if j = k then 1 else 0)
    (hγc : ∀ i j k, γ i j k = γ j i k)
    (hγa : ∀ i j l m, ∑ k, γ i j k * γ k l m = ∑ k, γ j l k * γ i k m)
    (hγd : ∀ i j k, i ≠ 0 → j ≠ 0 → (γ i j k).natDegree ≤ d i + d j - d k)
    (hγB : ∀ i j k, (γ i j k).map ρ = b.repr (b i * b j) k)
    (hε : ε ≠ 0) :
    ∃ γ' : Fin (n + 1) → Fin (n + 1) → Fin (n + 1) → A'[X],
      (∀ j k, γ' 0 j k = if j = k then 1 else 0) ∧
      (∀ i j k, γ' i j k = γ' j i k) ∧
      (∀ i j l m, ∑ k, γ' i j k * γ' k l m = ∑ k, γ' j l k * γ' i k m) ∧
      (∀ i j k, i ≠ 0 → j ≠ 0 → (γ' i j k).natDegree ≤ d i + d j - d k) ∧
      (∀ i j k, (γ' i j k).map π = γ i j k) := by
  classical

  have hρπ : Function.Surjective (ρ.comp π) := hρ.comp hπ
  have hπε : π ε = 0 := (hker ε).2 (dvd_refl ε)
  have hε2 : ε * ε = 0 := hsmall ε (by rw [hπε, map_zero])
  have hCε2 : (C ε : A'[X]) * C ε = 0 := by rw [← C_mul, hε2, C_0]
  have hunit : ∀ a : A', ρ (π a) ≠ 0 → IsUnit a := by
    intro a ha
    obtain ⟨a₁, ha₁⟩ := hρπ (ρ (π a))⁻¹
    have hm : IsNilpotent (a * a₁ - 1) := hnil _ (by
      rw [map_sub, map_mul, map_sub, map_mul, map_one, map_one]
      change ρ (π a) * (ρ.comp π) a₁ - 1 = 0
      rw [ha₁, mul_inv_cancel₀ ha, sub_self])
    have hu : IsUnit (a * a₁) := by
      have := hm.isUnit_one_add
      rwa [add_sub_cancel] at this
    exact isUnit_of_mul_isUnit_left hu
  have hann : ∀ a : A', ε * a = 0 → ρ (π a) = 0 := by
    intro a ha
    by_contra hne
    obtain ⟨u, rfl⟩ := hunit a hne
    exact hε (by simpa using congrArg (· * (↑u⁻¹ : A')) ha)

  set γB : Fin (n + 1) → Fin (n + 1) → Fin (n + 1) → K[X] := fun i j k => b.repr (b i * b j) k
    with hγBdef
  have hγB1 : ∀ j k, γB 0 j k = if j = k then 1 else 0 := repr_mul_unit b hb0
  have hγBc : ∀ i j k, γB i j k = γB j i k := fun i j k => by
    simp only [hγBdef, mul_comm]
  have hγBa : ∀ i j l m, ∑ k, γB i j k * γB k l m = ∑ k, γB j l k * γB i k m :=
    repr_mul_assoc b

  let sA : A → A' := sect0 π hπ
  have hsA0 : sA 0 = 0 := sect0_zero π hπ
  have hsA : ∀ a, π (sA a) = a := apply_sect0 π hπ
  let γ' : Fin (n + 1) → Fin (n + 1) → Fin (n + 1) → A'[X] := fun i j k =>
    if i = 0 then (if j = k then 1 else 0) else if j = 0 then (if i = k then 1 else 0)
      else liftPoly sA (γ i j k)
  have hγ'1 : ∀ j k, γ' 0 j k = if j = k then 1 else 0 := fun j k => by simp [γ']
  have hγ'1r : ∀ i k, γ' i 0 k = if i = k then 1 else 0 := fun i k => by
    by_cases hi : i = 0
    · subst hi; simp [γ']
    · simp [γ', hi]
  have hγ'c : ∀ i j k, γ' i j k = γ' j i k := by
    intro i j k
    by_cases hi : i = 0
    · subst hi; rw [hγ'1, hγ'1r]
    by_cases hj : j = 0
    · subst hj; rw [hγ'1, hγ'1r]
    simp only [γ', if_neg hi, if_neg hj, hγc i j k]
  have hγ'π : ∀ i j k, (γ' i j k).map π = γ i j k := by
    intro i j k
    by_cases hi : i = 0
    · subst hi; rw [hγ'1, hγ1]; split_ifs <;> simp
    by_cases hj : j = 0
    · subst hj; rw [hγ'1r, hγc, hγ1]; split_ifs <;> simp
    simp only [γ', if_neg hi, if_neg hj]
    exact map_liftPoly π sA hsA0 hsA _
  have hγ'd : ∀ i j k, i ≠ 0 → j ≠ 0 → (γ' i j k).natDegree ≤ d i + d j - d k := by
    intro i j k hi hj
    simp only [γ', if_neg hi, if_neg hj]
    exact (natDegree_liftPoly_le sA hsA0 _).trans (hγd i j k hi hj)
  have hγ'd0 : ∀ i j k, i = 0 ∨ j = 0 → (γ' i j k).natDegree = 0 := by
    rintro i j k (rfl | rfl)
    · rw [hγ'1]; split_ifs <;> simp
    · rw [hγ'1r]; split_ifs <;> simp

  have hdle : ∀ m, d m ≤ 2 := fun m => by
    by_cases hm : m = 0
    · rw [hm, hd0]; exact Nat.zero_le _
    · rcases hd m hm with h | h <;> omega
  have hdge : ∀ m, m ≠ 0 → 1 ≤ d m := fun m hm => by rcases hd m hm with h | h <;> omega

  let assoc' : Fin (n + 1) → Fin (n + 1) → Fin (n + 1) → Fin (n + 1) → A'[X] := fun i j l m =>
    (∑ k, γ' i j k * γ' k l m) - (∑ k, γ' j l k * γ' i k m)
  have hassoc'π : ∀ i j l m, (assoc' i j l m).map π = 0 := by
    intro i j l m
    simp only [assoc', Polynomial.map_sub, Polynomial.map_sum, Polynomial.map_mul, hγ'π]
    rw [hγa, sub_self]

  have hdegprod : ∀ i j k l m, i ≠ 0 → j ≠ 0 → l ≠ 0 →
      (γ' i j k * γ' k l m).natDegree ≤ d i + d j + d l - d m := by
    intro i j k l m hi hj hl
    by_cases hk : k = 0
    · subst hk
      rw [hγ'1]
      split_ifs with hlm
      · subst hlm
        have := hγ'd i j 0 hi hj
        rw [hd0] at this
        rw [mul_one]
        omega
      · rw [mul_zero, natDegree_zero]; exact Nat.zero_le _
    refine natDegree_mul_le.trans ?_
    · have h1 := hγ'd i j k hi hj
      have h2 := hγ'd k l m hk hl
      have := hdle k; have := hdle m; have := hdge k hk; have := hdge l hl
      have := hdge i hi; have := hdge j hj
      omega

  have hU1 : ∀ (j : Fin (n + 1)) (F : Fin (n + 1) → A'[X]), ∑ k, γ' 0 j k * F k = F j := by
    intro j F
    rw [Finset.sum_eq_single j]
    · rw [hγ'1, if_pos rfl, one_mul]
    · intro k _ hk; rw [hγ'1, if_neg (Ne.symm hk), zero_mul]
    · intro h; exact absurd (Finset.mem_univ j) h
  have hU2 : ∀ (m : Fin (n + 1)) (F : Fin (n + 1) → A'[X]), ∑ k, F k * γ' 0 k m = F m := by
    intro m F
    rw [Finset.sum_eq_single m]
    · rw [hγ'1, if_pos rfl, mul_one]
    · intro k _ hk; rw [hγ'1, if_neg hk, mul_zero]
    · intro h; exact absurd (Finset.mem_univ m) h
  have hU3 : ∀ (i : Fin (n + 1)) (F : Fin (n + 1) → A'[X]), ∑ k, γ' i 0 k * F k = F i := by
    intro i F
    rw [Finset.sum_eq_single i]
    · rw [hγ'1r, if_pos rfl, one_mul]
    · intro k _ hk; rw [hγ'1r, if_neg (Ne.symm hk), zero_mul]
    · intro h; exact absurd (Finset.mem_univ i) h
  have hU4 : ∀ (m : Fin (n + 1)) (F : Fin (n + 1) → A'[X]), ∑ k, F k * γ' k 0 m = F m := by
    intro m F
    rw [Finset.sum_eq_single m]
    · rw [hγ'1r, if_pos rfl, mul_one]
    · intro k _ hk; rw [hγ'1r, if_neg hk, mul_zero]
    · intro h; exact absurd (Finset.mem_univ m) h
  have hassoc'd : ∀ i j l m, (assoc' i j l m).natDegree ≤ d i + d j + d l - d m := by
    intro i j l m
    by_cases hi : i = 0
    · subst hi
      have : assoc' 0 j l m = 0 := by
        change (∑ k, γ' 0 j k * γ' k l m) - (∑ k, γ' j l k * γ' 0 k m) = 0
        rw [hU1 j (fun k => γ' k l m), hU2 m (fun k => γ' j l k), sub_self]
      rw [this, natDegree_zero]; exact Nat.zero_le _
    by_cases hj : j = 0
    · subst hj
      have : assoc' i 0 l m = 0 := by
        change (∑ k, γ' i 0 k * γ' k l m) - (∑ k, γ' 0 l k * γ' i k m) = 0
        rw [hU3 i (fun k => γ' k l m), hU1 l (fun k => γ' i k m), sub_self]
      rw [this, natDegree_zero]; exact Nat.zero_le _
    by_cases hl : l = 0
    · subst hl
      have : assoc' i j 0 m = 0 := by
        change (∑ k, γ' i j k * γ' k 0 m) - (∑ k, γ' j 0 k * γ' i k m) = 0
        rw [hU4 m (fun k => γ' i j k), hU3 j (fun k => γ' i k m), hγ'c i j m, sub_self]
      rw [this, natDegree_zero]; exact Nat.zero_le _
    refine (natDegree_sub_le _ _).trans (max_le ?_ ?_)
    · exact Polynomial.natDegree_sum_le_of_forall_le _ _ fun k _ => hdegprod i j k l m hi hj hl
    · refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun k _ => ?_
      have := hdegprod j l k i m hj hl hi
      have e : d j + d l + d i - d m = d i + d j + d l - d m := by omega
      rw [← e, hγ'c i k m]; exact this

  let ac : Fin (n + 1) → Fin (n + 1) → Fin (n + 1) → Fin (n + 1) → A'[X] := fun i j l m =>
    divPoly ε (assoc' i j l m)
  have hac : ∀ i j l m, (∑ k, γ' i j k * γ' k l m) - (∑ k, γ' j l k * γ' i k m) =
      C ε * ac i j l m := by
    intro i j l m
    change assoc' i j l m = C ε * divPoly ε (assoc' i j l m)
    rw [C_mul_divPoly]
    intro t
    rw [← hker]
    have := congrArg (fun F : A[X] => F.coeff t) (hassoc'π i j l m)
    simpa only [coeff_map, coeff_zero] using this
  have hacd : ∀ i j l m, (ac i j l m).natDegree ≤ d i + d j + d l - d m := fun i j l m =>
    (natDegree_divPoly_le ε _).trans (hassoc'd i j l m)

  haveI : Module.Finite K[X] B := Module.Finite.of_basis b
  haveI : FaithfulSMul K[X] B := by
    rw [faithfulSMul_iff_algebraMap_injective]
    intro f g hfg
    have h1 : ∀ f : K[X], b.repr (algebraMap K[X] B f) 0 = f := fun f => by
      rw [Algebra.algebraMap_eq_smul_one, ← hb0, map_smul, b.repr_self, Finsupp.smul_apply,
        Finsupp.single_eq_same, smul_eq_mul, mul_one]
    rw [← h1 f, ← h1 g, hfg]
  have hloc : ∀ P : Ideal K[X], P.IsMaximal → ∃ s : K[X], s ∉ P ∧
      ∃ φ : Fin (n + 1) → Fin (n + 1) → Fin (n + 1) → K[X],
        (∀ j k, φ 0 j k = 0) ∧ (∀ i j k, φ i j k = φ j i k) ∧
        ∀ i j l m, (∑ k, φ j l k * γB i k m) - (∑ k, γB i j k * φ k l m) +
          (∑ k, γB j l k * φ i k m) - (∑ k, φ i j k * γB k l m) =
            s * (ac i j l m).map (ρ.comp π) := by
    intro P hP
    have hmono := AlgebraicCurve.exists_aeval_sub_mem_smul_of_isMaximal_of_isIntegrallyClosed
      K B P hP
    exact AlgebraicCurve.exists_local_coboundary_of_smallExtension_of_monogenic_fibre K n B b hb0
      A' A π hπ ε hker ρ hρ hann γ hγ1 hγc hγa hγB γ' hγ'1 hγ'c hγ'π ac hac P hP hmono
  have hinfty := AlgebraicCurve.exists_coboundary_at_infinity_of_smallExtension_of_split K n B b
    d hb0 hd0 hd hdeg hinf A' A π hπ ε hker ρ hρ hann γ hγ1 hγc hγa hγd hγB γ' hγ'1 hγ'c hγ'π
    hγ'd ac hac hacd
  have hdisc := AlgebraicCurve.discr_ne_zero_of_normalForm_split K n B b d hb0 hd0 hd hdeg hinf
  have hgen : ∀ ψ : Fin (n + 1) → Fin (n + 1) → Fin (n + 1) → K[X],
      (∀ j k, ψ 0 j k = 0) → (∀ i j k, ψ i j k = ψ j i k) →
      (∀ i j l m, (∑ k, ψ j l k * γB i k m) - (∑ k, γB i j k * ψ k l m) +
          (∑ k, γB j l k * ψ i k m) - (∑ k, ψ i j k * γB k l m) = 0) →
      ∃ u : K[X], u ≠ 0 ∧ ∃ lam : Fin (n + 1) → Fin (n + 1) → K[X], (∀ m, lam 0 m = 0) ∧
        ∀ i j m, u * ψ i j m =
          (∑ k, lam j k * γB i k m) - (∑ k, γB i j k * lam k m) + (∑ k, lam i k * γB k j m) :=
    fun ψ h1 h2 h3 =>
      AlgebraicCurve.exists_mul_eq_hochschild_coboundary_of_discr_ne_zero K n B b hb0 hdisc ψ h1
        h2 h3
  obtain ⟨φ, hφ1, hφc, hφd, hφa⟩ :=
    AlgebraicCurve.exists_bounded_two_cochain_of_local_coboundaries K n d hd0 hd γB hγB1 hγBc
      hγBa hdeg (fun i j l m => (ac i j l m).map (ρ.comp π)) hloc hinfty hgen

  let sK : K → A' := sect0 (ρ.comp π) hρπ
  have hsK0 : sK 0 = 0 := sect0_zero _ hρπ
  have hsK : ∀ a, (ρ.comp π) (sK a) = a := apply_sect0 _ hρπ
  let φt : Fin (n + 1) → Fin (n + 1) → Fin (n + 1) → A'[X] := fun i j k =>
    if i = 0 ∨ j = 0 then 0 else liftPoly sK (φ i j k)
  have hφc0 : ∀ i k, φ i 0 k = 0 := fun i k => by rw [hφc, hφ1]
  have hφtred : ∀ i j k, (φt i j k).map (ρ.comp π) = φ i j k := by
    intro i j k
    by_cases h : i = 0 ∨ j = 0
    · simp only [φt, if_pos h, Polynomial.map_zero]
      rcases h with rfl | rfl
      · rw [hφ1]
      · rw [hφc0]
    · simp only [φt, if_neg h]
      exact map_liftPoly _ sK hsK0 hsK _
  have hφt0 : ∀ j k, φt 0 j k = 0 := fun j k => by simp [φt]
  have hφt0r : ∀ i k, φt i 0 k = 0 := fun i k => by simp [φt]
  have hφtc : ∀ i j k, φt i j k = φt j i k := by
    intro i j k
    by_cases h : i = 0 ∨ j = 0
    · have h' : j = 0 ∨ i = 0 := h.symm
      simp only [φt, if_pos h, if_pos h']
    · have h' : ¬(j = 0 ∨ i = 0) := fun h' => h h'.symm
      simp only [φt, if_neg h, if_neg h', hφc i j k]
  have hφtd : ∀ i j k, i ≠ 0 → j ≠ 0 → (φt i j k).natDegree ≤ d i + d j - d k := by
    intro i j k hi hj
    have h : ¬(i = 0 ∨ j = 0) := by tauto
    simp only [φt, if_neg h]
    exact (natDegree_liftPoly_le sK hsK0 _).trans (hφd i j k hi hj)
  have hγ'red : ∀ i j k, (γ' i j k).map (ρ.comp π) = γB i j k := fun i j k => by
    rw [← Polynomial.map_map, hγ'π, hγB]
  let γ'' : Fin (n + 1) → Fin (n + 1) → Fin (n + 1) → A'[X] := fun i j k =>
    γ' i j k + C ε * φt i j k

  let E : Fin (n + 1) → Fin (n + 1) → Fin (n + 1) → Fin (n + 1) → A'[X] := fun i j l m =>
    ((∑ k, γ' i j k * φt k l m) + ∑ k, φt i j k * γ' k l m) -
      ((∑ k, γ' j l k * φt i k m) + ∑ k, φt j l k * γ' i k m)
  have hexpand : ∀ x y z t : A'[X],
      (x + C ε * y) * (z + C ε * t) = x * z + C ε * (x * t + y * z) := by
    intro x y z t
    linear_combination (y * t) * hCε2
  have hassoc'' : ∀ i j l m,
      (∑ k, γ'' i j k * γ'' k l m) - (∑ k, γ'' j l k * γ'' i k m) =
        C ε * (ac i j l m + E i j l m) := by
    intro i j l m
    have e1 : ∑ k, γ'' i j k * γ'' k l m =
        (∑ k, γ' i j k * γ' k l m) + C ε * ((∑ k, γ' i j k * φt k l m) +
          ∑ k, φt i j k * γ' k l m) := by
      simp only [γ'', hexpand, Finset.sum_add_distrib, Finset.mul_sum, mul_add]
    have e2 : ∑ k, γ'' j l k * γ'' i k m =
        (∑ k, γ' j l k * γ' i k m) + C ε * ((∑ k, γ' j l k * φt i k m) +
          ∑ k, φt j l k * γ' i k m) := by
      simp only [γ'', hexpand, Finset.sum_add_distrib, Finset.mul_sum, mul_add]
    rw [e1, e2]
    have := hac i j l m
    simp only [E]
    linear_combination this
  have hEred : ∀ i j l m, (ac i j l m + E i j l m).map (ρ.comp π) = 0 := by
    intro i j l m
    have hD := hφa i j l m
    simp only [Polynomial.map_add, Polynomial.map_sub, Polynomial.map_sum, Polynomial.map_mul,
      hγ'red, hφtred, E]
    rw [← hD]
    ring
  have hkill : ∀ i j l m, C ε * (ac i j l m + E i j l m) = 0 := by
    intro i j l m
    ext t
    rw [coeff_C_mul, coeff_zero]
    apply hsmall
    have := congrArg (fun F : K[X] => F.coeff t) (hEred i j l m)
    simpa only [coeff_map, coeff_zero, RingHom.comp_apply] using this
  refine ⟨γ'', fun j k => ?_, fun i j k => ?_, fun i j l m => ?_, fun i j k hi hj => ?_,
    fun i j k => ?_⟩
  · simp only [γ'', hγ'1, hφt0, mul_zero, add_zero]
  · simp only [γ'', hγ'c i j k, hφtc i j k]
  · rw [← sub_eq_zero, hassoc'', hkill]
  · refine (natDegree_add_le _ _).trans (max_le (hγ'd i j k hi hj) ?_)
    exact (natDegree_C_mul_le _ _).trans (hφtd i j k hi hj)
  · simp only [γ'', Polynomial.map_add, Polynomial.map_mul, map_C, hπε, C_0, zero_mul, add_zero,
      hγ'π]

end Main

end SmallExtSol

end

open SmallExtSol in
theorem solution
    (K : Type u) [Field K] [IsAlgClosed K]
    (n : ℕ) (B : Type v) [CommRing B] [IsDomain B] [IsIntegrallyClosed B]
    [Algebra K[X] B] (b : Module.Basis (Fin (n + 1)) K[X] B) (d : Fin (n + 1) → ℕ)
    (hb0 : b 0 = 1) (hd0 : d 0 = 0) (hd : ∀ i, i ≠ 0 → d i = 1 ∨ d i = 2)
    (hdeg : ∀ i j k, i ≠ 0 → j ≠ 0 → ((b.repr (b i * b j)) k).natDegree ≤ d i + d j - d k)
    (hinf : ∃ τ : Fin (n + 1) → Fin (n + 1) → K,
      IsUnit (Matrix.det (Matrix.of τ)) ∧
      (∀ j, τ j 0 = 1) ∧
      ∀ j i i', i ≠ 0 → i' ≠ 0 →
        τ j i * τ j i' = ∑ k, ((b.repr (b i * b i')) k).coeff (d i + d i' - d k) * τ j k)
    (A' : Type w) [CommRing A'] (A : Type w') [CommRing A]
    (π : A' →+* A) (hπ : Function.Surjective π) (ε : A') (hker : ∀ a : A', π a = 0 ↔ ε ∣ a)
    (ρ : A →+* K) (hρ : Function.Surjective ρ)
    (hsmall : ∀ a : A', ρ (π a) = 0 → ε * a = 0)
    (hnil : ∀ a : A', ρ (π a) = 0 → IsNilpotent a)
    (γ : Fin (n + 1) → Fin (n + 1) → Fin (n + 1) → A[X])
    (hγ1 : ∀ j k, γ 0 j k = if j = k then 1 else 0)
    (hγc : ∀ i j k, γ i j k = γ j i k)
    (hγa : ∀ i j l m, ∑ k, γ i j k * γ k l m = ∑ k, γ j l k * γ i k m)
    (hγd : ∀ i j k, i ≠ 0 → j ≠ 0 → (γ i j k).natDegree ≤ d i + d j - d k)
    (hγB : ∀ i j k, (γ i j k).map ρ = b.repr (b i * b j) k) :
    ∃ γ' : Fin (n + 1) → Fin (n + 1) → Fin (n + 1) → A'[X],
      (∀ j k, γ' 0 j k = if j = k then 1 else 0) ∧
      (∀ i j k, γ' i j k = γ' j i k) ∧
      (∀ i j l m, ∑ k, γ' i j k * γ' k l m = ∑ k, γ' j l k * γ' i k m) ∧
      (∀ i j k, i ≠ 0 → j ≠ 0 → (γ' i j k).natDegree ≤ d i + d j - d k) ∧
      (∀ i j k, (γ' i j k).map π = γ i j k) := by
  by_cases hε : ε = 0
  ·
    subst hε
    have hinj : Function.Injective π := by
      intro x y hxy
      have : π (x - y) = 0 := by rw [map_sub, hxy, sub_self]
      rw [hker, zero_dvd_iff, sub_eq_zero] at this
      exact this
    let e : A' ≃+* A := RingEquiv.ofBijective π ⟨hinj, hπ⟩
    have he : ∀ x, π (e.symm x) = x := fun x => e.apply_symm_apply x
    have hcomp : π.comp (e.symm : A ≃+* A').toRingHom = RingHom.id A := by
      ext x; exact he x
    refine ⟨fun i j k => (γ i j k).map (e.symm : A ≃+* A').toRingHom, fun j k => ?_,
      fun i j k => ?_, fun i j l m => ?_, fun i j k hi hj => ?_, fun i j k => ?_⟩
    · dsimp only
      rw [hγ1]; split_ifs <;> simp
    · dsimp only
      rw [hγc]
    · dsimp only
      have h := congrArg (Polynomial.map (e.symm : A ≃+* A').toRingHom) (hγa i j l m)
      simpa only [Polynomial.map_sum, Polynomial.map_mul] using h
    · dsimp only
      rw [natDegree_map_eq_of_injective (RingEquiv.injective _)]; exact hγd i j k hi hj
    · dsimp only
      rw [Polynomial.map_map, hcomp, Polynomial.map_id]
  · exact main b d hb0 hd0 hd hdeg hinf A' A π hπ ε hker ρ hρ hsmall hnil γ hγ1 hγc hγa hγd hγB hε

end S_AlgebraicCurve_exists_lift_normalForm_structureConstants_of_smallExtension
end P2MW
export P2MW.S_AlgebraicCurve_exists_lift_normalForm_structureConstants_of_smallExtension (solution)
